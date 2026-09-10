// SysML v2 / KerML language client: a thin shell around `sysmlv2 lsp`.
// Everything interesting (highlighting, diagnostics, outline, formatting)
// comes from the server's capabilities — this file only starts it.

const { workspace } = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");

let client;

function activate() {
  const command = workspace.getConfiguration("sysmlv2").get("serverPath", "sysmlv2");
  client = new LanguageClient(
    "sysmlv2",
    "sysmlv2 language server",
    { command, args: ["lsp"] },
    {
      documentSelector: [{ language: "sysml" }, { language: "kerml" }],
    }
  );
  client.start();
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
