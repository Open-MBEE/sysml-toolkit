//! What accepting a completion item writes, decided once per request
//! ([`Accept::new`]) and then per item ([`Accept::name`]): the range the
//! accepted text replaces, the text itself — the name spelled as source,
//! quoted where the name needs it — the statement repairs riding along
//! (see [`crate::autofix`]), and the text an editor filters the item by.
//!
//! **Range.** The partial word, extended backward over characters of
//! the candidate's own spelling: a typed `m/s` is replaced whole by
//! `'m/s²'`. Inside a quoted name being typed (`['metre per sec|`) the
//! range is the typed quoted spelling from its opening quote — through
//! the closing quote when the line holds one, as an editor that
//! auto-closes quotes leaves it, else through the rest of the word the
//! cursor sits in — so the accepted name replaces every word typed, not
//! the last one, and never leaves a quote or a word fragment behind.
//!
//! **Insert and replace.** With the cursor inside a word (`Mas|sValue`),
//! a client that takes insert/replace edits gets both ranges — insert
//! up to the cursor, replace through the rest of the word — and its own
//! setting picks one; other clients get the insert range, as before.
//! Items this module does not edit (keywords) get the same two ranges
//! from [`word_edits`]. A repair that would land where the replace range
//! ends rides the main edit then, since as a separate edit it would
//! overlap the replacement: right for the replacing accept, while an
//! inserting one leaves the rest of the word behind either way. Inside
//! a quoted name being typed the one range is replaced whole.
//!
//! **Filtering.** An editor refilters an open list by the text typed
//! since each item's range start, spaces included, and keeps the list
//! open while any item matches. A name containing whitespace (a model's
//! own `'Vehicle One'`) filters by its spelling with the whitespace
//! replaced (`Vehicle_One`): typing its first word, or any of its words,
//! still finds it, but a typed space matches no item and closes the
//! list, so the next word opens a fresh list instead of being filtered
//! against a stale one — whose first item Enter would accept. Inside a
//! quoted name a space belongs to the name, and the text typed from the
//! opening quote is matched against each item's quoted spelling. So it
//! does for a unit name typed word by word without its quotes inside a
//! bracket (`[metre per|`): once the words typed begin the name, its
//! range covers them and it filters by its own spelling, so the next
//! list — opened on the word after the space — still finds it. Only
//! there: the item's editor match then runs over every word typed, so
//! it outranks anything matching the partial word alone, and outside a
//! bracket the words before it usually mean something else — a type
//! followed by `ordered`, a feature followed by `then`, a keyword
//! followed by a declared name — which accepting would replace. Outside
//! a bracket such a name is typed from its opening quote.
//!
//! The repairs depend on where the replacement starts, and nearly every
//! item of a request starts at the same place — only a restricted name
//! reaching back over its own characters differs — so the statement is
//! scanned once per distinct start, not once per item.

use crate::autofix::{Repairs, statement_repairs};
use crate::nav::CompletionCx;
use crate::position::{Encoding, Mapper, offset32};
use lsp_types::{
    CompletionItem, CompletionTextEdit, InsertReplaceEdit, InsertTextFormat, TextEdit,
};
use std::cell::RefCell;
use sysmlv2_parser::ast::Dialect;
use sysmlv2_parser::span::Span;

#[cfg(test)]
thread_local! {
    /// Reads of the quoted name the cursor is typing, on this thread, so
    /// a test can pin what one completion request costs.
    pub(crate) static QUOTE_READS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// A quoted name the cursor is typing: `'metre per sec|`, or with the
/// closing quote an editor inserts along with the opening one,
/// `'metre per sec|'`.
#[derive(Clone, Copy)]
pub(crate) struct Quoted {
    /// The opening quote.
    open: u32,
    /// Just past the closing quote, when the cursor's line holds one.
    close_end: Option<u32>,
}

impl Quoted {
    /// Where the opening quote is.
    pub(crate) fn open(&self) -> u32 {
        self.open
    }
}

/// Where accepted text goes, decided once per request: the partial
/// word, and the quoted name being typed around it, if any.
pub(crate) struct Replacement {
    partial_start: u32,
    offset: u32,
    /// The identifier characters around the cursor: where an editor's
    /// own insertion of a label starts (`word_start..offset`), and the
    /// rest of the word the cursor sits in (`offset..word_end`).
    word_start: u32,
    word_end: u32,
    quoted: Option<Quoted>,
    /// The partial word sits inside an open bracket, where a unit is
    /// written (see [`Self::typed_words`]).
    in_bracket: bool,
}

impl Replacement {
    pub(crate) fn new(text: &str, cx: &CompletionCx) -> Replacement {
        let (word_start, word_end) = word_around(text, cx.offset);
        Replacement {
            partial_start: cx.partial_start,
            offset: cx.offset,
            word_start,
            word_end,
            quoted: cx.quoted,
            in_bracket: cx.in_bracket,
        }
    }

    /// Where accepting `name` starts replacing: the opening quote of a
    /// quoted name being typed; for a unit name containing whitespace
    /// typed word by word without its quotes, its first word (see
    /// [`Self::typed_words`]); else the partial word extended backward
    /// over characters of `name`'s own spelling — self-limiting: `3*m`
    /// stops at the `*` no unit name contains.
    pub(crate) fn start_for(&self, text: &str, name: &str) -> u32 {
        if let Some(q) = &self.quoted {
            return q.open;
        }
        if let Some(start) = self.typed_words(text, name) {
            return start;
        }
        let mut start = self.partial_start as usize;
        while let Some(prev) = text[..start].chars().next_back() {
            if prev.is_whitespace() || prev == '\'' || !name.contains(prev) {
                break;
            }
            start -= prev.len_utf8();
        }
        offset32(start)
    }

    /// Where `name`, a name containing whitespace, starts when it is
    /// being typed word by word without its quotes inside a bracket
    /// (`[metre per|` for `'metre per second squared'`): the word
    /// furthest back on the line from which the text typed up to the
    /// cursor begins the name, case aside. `None` outside a bracket (see
    /// the module notes), and when no word before the partial one does.
    fn typed_words(&self, text: &str, name: &str) -> Option<u32> {
        if !self.in_bracket || !name.contains(char::is_whitespace) {
            return None;
        }
        // No word typed before the partial one: nothing to take.
        let mut at = self.partial_start as usize;
        if text[..at].trim_end_matches([' ', '\t']).len() == at {
            return None;
        }
        let name = name.to_lowercase();
        let in_name = |c: char| c.to_lowercase().all(|l| name.contains(l));
        let typed_to = self.offset as usize;
        let mut found = None;
        loop {
            // Back over the spaces before this word, then over the
            // word before them, as far as the name's own characters go.
            let spaced = text[..at].trim_end_matches([' ', '\t']).len();
            if spaced == at {
                break;
            }
            let mut word = spaced;
            while let Some(c) = text[..word].chars().next_back() {
                if c.is_whitespace() || !in_name(c) {
                    break;
                }
                word -= c.len_utf8();
            }
            if word == spaced {
                break;
            }
            if name.starts_with(&text[word..typed_to].to_lowercase()) {
                found = Some(offset32(word));
            }
            at = word;
        }
        found
    }

    /// Where the replacement ends: past the closing quote of a quoted
    /// name being typed (the accepted spelling brings its own), through
    /// the rest of the word the cursor sits in when the line holds no
    /// closing quote — inside the quotes that word is part of the name
    /// being replaced — else the cursor. What follows is the
    /// statement's tail.
    pub(crate) fn end(&self) -> u32 {
        match &self.quoted {
            Some(q) => q.close_end.unwrap_or(self.word_end),
            None => self.offset,
        }
    }

    /// Where a replacing accept ends: through the rest of the word the
    /// cursor sits in — or, inside a quoted name being typed, where
    /// [`Self::end`] does: that replacement is whole either way.
    fn replace_end(&self) -> u32 {
        match &self.quoted {
            Some(_) => self.end(),
            None => self.word_end,
        }
    }
}

/// The identifier characters around `offset`: where the word the
/// cursor sits in starts and ends.
fn word_around(text: &str, offset: u32) -> (u32, u32) {
    let bytes = text.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let at = (offset as usize).min(bytes.len());
    let mut start = at;
    while start > 0 && is_ident(bytes[start - 1]) {
        start -= 1;
    }
    let mut end = at;
    while end < bytes.len() && is_ident(bytes[end]) {
        end += 1;
    }
    (offset32(start), offset32(end))
}

/// The quoted name the cursor at `offset` is typing, its opening quote
/// at `open` — found on the tokens of the text ahead of the cursor
/// (see [`crate::site::Scan::quote`]) — and the rest of the line may
/// close it. A quote that leaves the rest of the line with an
/// unterminated quoted name opens that name instead of closing this one
/// (`'Wid| + 'Gadget';` would pair the typed quote with the opening one
/// of `'Gadget'`): no closing quote then. A string spanning lines that
/// closes past the cursor reads, up to it, as one left open, so an
/// apostrophe earlier on the cursor's line inside it is taken for the
/// quote being typed (`it's m/|` gives `it'm/s²'`) — a rare case, and
/// one where completion has nothing to offer anyway.
pub(crate) fn quoted_from(text: &str, open: u32, offset: u32) -> Option<Quoted> {
    use sysmlv2_parser::token::TokenKind;
    #[cfg(test)]
    QUOTE_READS.with(|n| n.set(n.get() + 1));
    let at = offset as usize;
    let line_end = text.get(at..)?.find('\n').map_or(text.len(), |i| at + i);
    let line = text.get(open as usize..line_end)?;
    let tokens = sysmlv2_parser::lexer::tokenize(line).0;
    let (name, rest) = tokens.split_first()?;
    let reopens = rest
        .iter()
        .any(|t| t.kind == TokenKind::Error && line[t.span.start as usize..].starts_with('\''));
    Some(Quoted {
        open,
        close_end: (name.kind == TokenKind::UnrestrictedName && !reopens)
            .then(|| open + name.span.end),
    })
}

/// One request's completion accepts: the document, where accepted text
/// goes, and what the client takes.
pub(crate) struct Accept<'a> {
    text: &'a str,
    mapper: Mapper<'a>,
    dialect: Dialect,
    stmt_start: u32,
    at: Replacement,
    /// The client takes snippet syntax: a repair suffix riding the main
    /// edit carries a `$0` stop ahead of it.
    snippets: bool,
    /// The client takes insert/replace edits.
    insert_replace: bool,
    /// Statement repairs by replacement start.
    repairs: RefCell<Vec<(u32, Option<Repairs>)>>,
}

/// The edits accepting one item performs; [`Self::fill`] puts them on
/// the item.
#[derive(Default)]
pub(crate) struct ItemEdits {
    /// The main edit; `None` when inserting the label over the word
    /// being completed is exactly right.
    pub text_edit: Option<CompletionTextEdit>,
    /// A repair landing behind the main edit.
    pub repair: Option<TextEdit>,
    /// Snippet format, when the main edit carries a cursor stop.
    pub insert_text_format: Option<InsertTextFormat>,
    /// The text the item is filtered by, when its label will not do.
    pub filter_text: Option<String>,
}

impl ItemEdits {
    /// `item` with these edits, the `imports` its name needs riding
    /// ahead of the repair. Every tier completes its items here, so
    /// none can drop a field — the filter text least of all, without
    /// which a typed space keeps a list open again.
    pub(crate) fn fill(self, item: CompletionItem, imports: Vec<TextEdit>) -> CompletionItem {
        let additional: Vec<TextEdit> = imports.into_iter().chain(self.repair).collect();
        CompletionItem {
            text_edit: self.text_edit,
            additional_text_edits: (!additional.is_empty()).then_some(additional),
            insert_text_format: self.insert_text_format,
            filter_text: self.filter_text,
            ..item
        }
    }
}

impl<'a> Accept<'a> {
    pub(crate) fn new(
        text: &'a str,
        enc: Encoding,
        cx: &CompletionCx,
        dialect: Dialect,
        snippets: bool,
        insert_replace: bool,
    ) -> Accept<'a> {
        Accept {
            text,
            mapper: Mapper::new(text, enc),
            dialect,
            stmt_start: cx.stmt_start,
            at: Replacement::new(text, cx),
            snippets,
            insert_replace,
            repairs: RefCell::new(Vec::new()),
        }
    }

    /// Accepting `name`. Insert text is source for this document: a
    /// name the dialect reserves (`'view'`) and a non-basic name
    /// (`'m/s²'` — the raw label would parse as an expression) insert
    /// quoted, over the typed spelling (see [`Replacement::start_for`]);
    /// a word the dialect does not reserve stays bare, even where it was
    /// typed quoted. No main edit for a basic name needing no repairs:
    /// plain label insertion is right and keeps the item light.
    pub(crate) fn name(&self, name: &str) -> ItemEdits {
        let spelled = sysmlv2_parser::name::spell_name_in(Some(self.dialect), name);
        let start = self.at.start_for(self.text, name);
        let plain = spelled == name;
        self.edits(name, spelled, start, plain)
    }

    /// Accepting the item named `name` by inserting `spelled` — source
    /// text already, such as an import's qualified path — over the
    /// partial word, or the quoted name being typed.
    pub(crate) fn spelled(&self, name: &str, spelled: String) -> ItemEdits {
        let start = self
            .at
            .quoted
            .as_ref()
            .map_or(self.at.partial_start, |q| q.open);
        self.edits(name, spelled, start, false)
    }

    /// The main edit writing `spelled` from `start`, with the statement
    /// repairs riding along: the suffix on the main edit, the rest as a
    /// separate insertion past it. When a repair suffix rides the main
    /// edit and the client takes snippets, the edit carries a `$0` stop
    /// between the text and the suffix: the cursor belongs where typing
    /// continues, before the auto-inserted `]`, not after it. `plain`:
    /// the editor's own insertion of the label would write `spelled`.
    fn edits(&self, name: &str, spelled: String, start: u32, plain: bool) -> ItemEdits {
        let range = Span::new(start, self.at.end());
        let replace_end = self.at.replace_end();
        // Mid-word, for a client that takes both: insert and replace.
        let both = self.insert_replace && replace_end != range.end;
        let (mut suffix, mut insert) = match self.repairs(start) {
            Some(r) => (r.suffix, r.insert),
            None => (String::new(), None),
        };
        // A repair landing where the replaced word ends would overlap
        // the replacement: it rides the main edit instead, right for the
        // replacing accept (`[m|s` → `['m/s²']`); inserting mid-word
        // leaves the rest of the word behind either way.
        if both {
            if let Some((_, fix)) = insert.take_if(|(at, _)| *at <= replace_end) {
                suffix.push_str(&fix);
            }
        }
        let snippet = self.snippets && !suffix.is_empty();
        // What an editor inserts for an item without an edit: its label
        // over the word before the cursor.
        let default_range = range == Span::new(self.at.word_start, self.at.offset);
        let text_edit = (!plain || !suffix.is_empty() || !default_range || both).then(|| {
            let new_text = if snippet {
                format!("{}$0{suffix}", snippet_escape(&spelled))
            } else {
                format!("{spelled}{suffix}")
            };
            let insert = self.mapper.range(range);
            if both {
                CompletionTextEdit::InsertAndReplace(InsertReplaceEdit {
                    new_text,
                    insert,
                    replace: self.mapper.range(Span::new(start, replace_end)),
                })
            } else {
                CompletionTextEdit::Edit(TextEdit {
                    range: insert,
                    new_text,
                })
            }
        });
        ItemEdits {
            text_edit,
            repair: insert.map(|(at, fix)| TextEdit {
                range: self.mapper.range(Span::new(at, at)),
                new_text: fix,
            }),
            insert_text_format: snippet.then_some(InsertTextFormat::SNIPPET),
            filter_text: match self.at.quoted {
                Some(_) => Some(quoted_spelling(name)),
                // Typed word by word: the text an editor matches holds
                // the name's own spaces.
                None if self.text[start as usize..self.at.offset as usize]
                    .contains(char::is_whitespace) =>
                {
                    None
                }
                None => name
                    .contains(char::is_whitespace)
                    .then(|| name.replace(char::is_whitespace, "_")),
            },
        }
    }

    /// The statement repairs for a replacement starting at `start`,
    /// scanned on first use. The scan reads the statement up to `start`
    /// — before any opening quote the replacement absorbs, so it never
    /// sees a dangling quoted name — and the tail from the
    /// replacement's end.
    fn repairs(&self, start: u32) -> Option<Repairs> {
        let mut memo = self.repairs.borrow_mut();
        if let Some((_, known)) = memo.iter().find(|(s, _)| *s == start) {
            return known.clone();
        }
        let scanned = statement_repairs(self.text, self.stmt_start, start, self.at.end());
        memo.push((start, scanned.clone()));
        scanned
    }
}

/// With the cursor at `offset` inside a word, give each item left to the
/// editor's default insertion — its label over the partial word, no
/// edit of its own, as keywords are — the insert and replace ranges
/// [`Accept`] gives the items it edits. For a client that takes
/// insert/replace edits only.
pub(crate) fn word_edits(items: &mut [CompletionItem], text: &str, offset: u32, enc: Encoding) {
    let (start, end) = word_around(text, offset);
    if end == offset {
        return;
    }
    let mapper = Mapper::new(text, enc);
    let insert = mapper.range(Span::new(start, offset));
    let replace = mapper.range(Span::new(start, end));
    for item in items.iter_mut().filter(|i| i.text_edit.is_none()) {
        let new_text = item
            .insert_text
            .take()
            .unwrap_or_else(|| item.label.clone());
        item.text_edit = Some(CompletionTextEdit::InsertAndReplace(InsertReplaceEdit {
            new_text,
            insert,
            replace,
        }));
    }
}

/// `name` spelled as a quoted name whatever its form (`'Widget'`,
/// `'metre per second'`): the text typed inside a quoted name is
/// matched against it.
fn quoted_spelling(name: &str) -> String {
    let escaped = sysmlv2_parser::ast::escape_name(name);
    if escaped.starts_with('\'') {
        escaped
    } else {
        format!("'{escaped}'")
    }
}

/// A completion's literal text made safe for snippet-format delivery:
/// `$`, `}`, and `\` are snippet syntax and must arrive escaped.
fn snippet_escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        if matches!(c, '$' | '}' | '\\') {
            out.push('\\');
        }
        out.push(c);
    }
    out
}
