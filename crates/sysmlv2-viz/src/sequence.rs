//! Sequence view, mirroring the Pilot visualizer's SEQUENCE
//! mode: lifelines for the parts that exchange messages, `->>` arrows
//! for flow-family usages (the `message` spelling included), ordered
//! by the events' succession partial order.
//!
//! Each message end resolves through [`ResolvedModel`]'s connector-end
//! machinery to a written feature chain; an end whose last link is an
//! event (occurrence-family usage) contributes (participant = the
//! previous link, or the event's owner; event = the last link) — the
//! canonical `message m from producer.pub_evt to server.rcv_evt`
//! shape. A non-event end falls back to its deepest part-family link,
//! so plain `flow` / `message` arrows between parts still render.
//!
//! Ordering: explicit successions between events add edges, and a bare
//! leading `then` between two sibling events (`event occurrence a;
//! then event occurrence b;` — an all-empty-ends succession, adjacency
//! positional) links the neighbours. Messages are stable-sorted by the
//! transitive reachability of their events, so a lifeline's declared
//! event order wins over message declaration order.
//!
//! Participants are grouped `box "Owner" … end box` by their owning
//! definition/usage (the Pilot boxes per traversed occurrence
//! definition); package-owned participants stay unboxed. The sequence
//! dialect accepts no direction line, so `--horizontal` is ignored.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use sysmlv2_model::json::{ElementRef, ResolvedModel};

use crate::{VizOptions, escape, inline_label, payload_label, usage_label};

/// Flow-family metaclasses drawn as message arrows.
const FLOWS: &[&str] = &["FlowUsage", "SuccessionFlowUsage", "Flow", "SuccessionFlow"];

/// Occurrence-family metaclasses accepted as message events.
const EVENTS: &[&str] = &["EventOccurrenceUsage", "OccurrenceUsage"];

/// Usage metaclasses accepted as participants (lifelines).
const PARTICIPANTS: &[&str] = &[
    "PartUsage",
    "ItemUsage",
    "OccurrenceUsage",
    "ReferenceUsage",
    "Usage",
];

pub(crate) fn emit(r: &mut ResolvedModel, tops: &[ElementRef], opts: &VizOptions) -> String {
    let mut em = Emitter {
        r,
        opts,
        participants: Vec::new(),
        messages: Vec::new(),
        order: HashMap::new(),
    };
    for &e in tops {
        em.collect(e);
    }
    em.sort_messages();
    em.render()
}

/// One end of a message: the lifeline it lands on and, when the end
/// was spelled through an event, that event (for ordering).
struct End {
    participant: ElementRef,
    event: Option<ElementRef>,
}

struct Message {
    from: End,
    to: End,
    label: String,
}

struct Emitter<'a> {
    r: &'a mut ResolvedModel,
    opts: &'a VizOptions,
    /// Lifelines in first-use order.
    participants: Vec<ElementRef>,
    messages: Vec<Message>,
    /// event → its succession successors.
    order: HashMap<ElementRef, Vec<ElementRef>>,
}

impl Emitter<'_> {
    /// Walk the whole subtree: everything is a transparent container;
    /// flows become messages, successions order events.
    fn collect(&mut self, e: ElementRef) {
        let members = self.r.owned_members(e);
        // A bare leading `then` between sibling events is an
        // all-empty-ends succession; adjacency carries the order.
        let mut prev_event: Option<ElementRef> = None;
        let mut pending_then = false;
        for &m in &members {
            let ty = self.r.element_type(m);
            if EVENTS.contains(&ty) {
                if pending_then {
                    if let Some(prev) = prev_event {
                        self.order.entry(prev).or_default().push(m);
                    }
                }
                prev_event = Some(m);
                pending_then = false;
            } else if ty == "SuccessionAsUsage" || ty == "Succession" {
                let ends = self.r.connector_end_targets(m);
                let all_bare = ends
                    .iter()
                    .all(|end| end.chain.is_empty() && end.spelling.is_none());
                if all_bare && prev_event.is_some() {
                    pending_then = true;
                } else {
                    self.record_succession(m);
                    prev_event = None;
                    pending_then = false;
                }
            } else {
                if FLOWS.contains(&ty) {
                    self.record_message(m);
                }
                prev_event = None;
                pending_then = false;
            }
        }
        for m in members {
            self.collect(m);
        }
    }

    /// An explicit succession between events adds ordering edges.
    fn record_succession(&mut self, e: ElementRef) {
        let ends = self.r.connector_end_targets(e);
        if ends.len() < 2 {
            return;
        }
        let last_link = |end: &sysmlv2_model::json::ConnectorEndTarget| end.chain.last().copied();
        let (Some(src), Some(tgt)) = (
            ends.first().and_then(last_link),
            ends.last().and_then(last_link),
        ) else {
            return;
        };
        if EVENTS.contains(&self.r.element_type(src)) && EVENTS.contains(&self.r.element_type(tgt))
        {
            self.order.entry(src).or_default().push(tgt);
        }
    }

    /// Split one message end chain into (participant, event).
    fn split_end(&mut self, chain: &[ElementRef]) -> Option<End> {
        let &last = chain.last()?;
        if EVENTS.contains(&self.r.element_type(last)) {
            let participant = if chain.len() >= 2 {
                chain[chain.len() - 2]
            } else {
                self.r.owner(last)?
            };
            return Some(End {
                participant,
                event: Some(last),
            });
        }
        // Not an event end: the deepest part-family link is the lifeline.
        let participant = chain
            .iter()
            .rev()
            .copied()
            .find(|&l| PARTICIPANTS.contains(&self.r.element_type(l)))?;
        Some(End {
            participant,
            event: None,
        })
    }

    fn record_message(&mut self, e: ElementRef) {
        let ends = self.r.connector_end_targets(e);
        if ends.len() < 2 {
            return;
        }
        let Some(from) = self.split_end(&ends.first().cloned().unwrap().chain) else {
            return;
        };
        let Some(to) = self.split_end(&ends.last().cloned().unwrap().chain) else {
            return;
        };
        for p in [from.participant, to.participant] {
            if !self.participants.contains(&p) {
                self.participants.push(p);
            }
        }
        let label = self
            .r
            .element_name(e)
            .map(str::to_string)
            .or_else(|| payload_label(self.r, e))
            .unwrap_or_default();
        self.messages.push(Message { from, to, label });
    }

    /// Does `from` reach `to` through the succession order?
    fn reaches(&self, from: ElementRef, to: ElementRef, seen: &mut HashSet<ElementRef>) -> bool {
        if !seen.insert(from) {
            return false;
        }
        let Some(nexts) = self.order.get(&from) else {
            return false;
        };
        for &n in nexts {
            if n == to || self.reaches(n, to, seen) {
                return true;
            }
        }
        false
    }

    /// `-1` when some event of `a` precedes an event of `b`.
    fn compare(&self, a: &Message, b: &Message) -> i32 {
        let events = |m: &Message| {
            [m.from.event, m.to.event]
                .into_iter()
                .flatten()
                .collect::<Vec<_>>()
        };
        for ea in events(a) {
            for eb in events(b) {
                if self.reaches(ea, eb, &mut HashSet::new()) {
                    return -1;
                }
                if self.reaches(eb, ea, &mut HashSet::new()) {
                    return 1;
                }
            }
        }
        0
    }

    /// Stable insertion sort under the partial order — declaration
    /// order breaks ties (the Pilot sorts its messages the same way).
    fn sort_messages(&mut self) {
        for i in 1..self.messages.len() {
            let mut j = i;
            while j > 0 && self.compare(&self.messages[j - 1], &self.messages[j]) > 0 {
                self.messages.swap(j - 1, j);
                j -= 1;
            }
        }
    }

    fn render(self) -> String {
        let mut out = String::from("@startuml\n");
        // Group lifelines by owner (first-use order); a named non-package
        // owner draws a `box`.
        let mut owners: Vec<Option<ElementRef>> = Vec::new();
        let mut groups: HashMap<Option<ElementRef>, Vec<ElementRef>> = HashMap::new();
        let mut alias: HashMap<ElementRef, String> = HashMap::new();
        for (i, &p) in self.participants.iter().enumerate() {
            alias.insert(p, format!("n{}", i + 1));
            let owner = self.r.owner(p).filter(|&o| {
                !matches!(
                    self.r.element_type(o),
                    "Package" | "LibraryPackage" | "Namespace"
                ) && self.r.element_name(o).is_some()
            });
            if !owners.contains(&owner) {
                owners.push(owner);
            }
            groups.entry(owner).or_default().push(p);
        }
        for owner in owners {
            if let Some(o) = owner {
                let name = escape(self.r.element_name(o).unwrap_or(""));
                let _ = writeln!(out, "box \"{name}\"");
            }
            for p in &groups[&owner] {
                let label = usage_label(self.r, *p);
                let label = if label.trim().is_empty() {
                    "(participant)".to_string()
                } else {
                    label
                };
                let link = crate::link_suffix(self.r, self.opts, *p);
                let _ = writeln!(
                    out,
                    "participant \"{}\" as {}{link}",
                    escape(&label),
                    alias[p]
                );
            }
            if owner.is_some() {
                out.push_str("end box\n");
            }
        }
        for m in &self.messages {
            let suffix = if m.label.trim().is_empty() {
                String::new()
            } else {
                format!(" : {}", inline_label(&m.label))
            };
            let _ = writeln!(
                out,
                "{} ->> {}{suffix}",
                alias[&m.from.participant], alias[&m.to.participant]
            );
        }
        out.push_str("@enduml\n");
        out
    }
}
