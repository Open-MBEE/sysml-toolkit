# SysML v2 / KerML for VS Code

Language support for the OMG SysML v2 and KerML textual notations, powered by the `sysmlv2` language server (`sysmlv2 lsp`).

- **Exact, dialect-aware highlighting** via semantic tokens. Keywords in this language are contextual — `part` is a keyword in SysML and a legal name in KerML — so no TextMate grammar can classify them; the parser does, and this extension renders its verdict. The bundled TextMate grammar is a deliberately coarse fallback (notes, doc comments, strings, numbers) shown only until the server answers.
- **Live diagnostics** on every keystroke: parse errors with recovery (the file keeps working while broken) plus body-context validation.
- **Outline / breadcrumbs / sticky scroll** from the document symbol tree, including anonymous members (`«part»`) and `: Type [mult]` details.
- **Formatting** via the toolkit's idempotent, note-preserving formatter.

## Setup

1. Install the `sysmlv2` binary somewhere on `PATH` (or set `sysmlv2.serverPath`). The default release binary includes the server; check with `sysmlv2 lsp --help`.
2. Build and install the extension:

   ```sh
   cd editors/vscode
   npm install
   npx vsce package        # produces sysmlv2-<version>.vsix
   code --install-extension sysmlv2-*.vsix
   ```

## Other editors

The server is plain LSP over stdio; any client works.

**Neovim** (0.11+):

```lua
vim.filetype.add { extension = { sysml = "sysml", kerml = "kerml" } }
vim.lsp.config("sysmlv2", {
  cmd = { "sysmlv2", "lsp" },
  filetypes = { "sysml", "kerml" },
})
vim.lsp.enable("sysmlv2")
```

**Helix** (`languages.toml`):

```toml
[language-server.sysmlv2]
command = "sysmlv2"
args = ["lsp"]

[[language]]
name = "sysml"
scope = "source.sysml"
file-types = ["sysml", "kerml"]
language-servers = ["sysmlv2"]
```
