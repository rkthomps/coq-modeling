from __future__ import annotations
import sys
import threading
import subprocess
import time
import ipdb

from coqpyt.coq.structs import Step
from coqpyt.lsp.structs import *
from coqpyt.lsp.json_rpc_endpoint import JsonRpcEndpoint
from coqpyt.lsp.endpoint import LspEndpoint
from coqpyt.lsp.client import LspClient
from coqpyt.coq.lsp.structs import *


class ClientWrapper:
    def __init__(self, client: FastLspClient, file_uri: str) -> None:
        self.client = client
        self.file_uri = file_uri
        self.file_version = 1
        self.client.didOpen(
            TextDocumentItem(self.file_uri, "coq", self.file_version, "")
        )

    def set_version(self, v: int) -> None:
        self.file_version = v

    def write(self, content: str) -> None:
        self.file_version += 1
        self.client.didChange(
            VersionedTextDocumentIdentifier(self.file_uri, self.file_version),
            [TextDocumentContentChangeEvent(None, None, content)],
        )

    def write_and_get_steps(self, content: str) -> list[Step]:
        self.write(content)
        lines = content.split("\n")
        spans = self.client.get_document(TextDocumentIdentifier(self.file_uri)).spans
        steps: list[Step] = []
        prev_line, prev_char = (0, 0)
        try:
            for i, span in enumerate(spans):
                # if i == len(spans) - 1 and span.span is None:
                #     continue
                end_line, end_char = (
                    spans[i].range.end.line,
                    spans[i].range.end.character,
                )
                cur_lines = lines[prev_line : (end_line + 1)].copy()
                cur_lines[-1] = cur_lines[-1][:end_char]
                cur_lines[0] = cur_lines[0][prev_char:]
                prev_line, prev_char = end_line, end_char
                text = "\n".join(cur_lines)
                steps.append(Step(text, "", span))
            return steps[:-1]
        except IndexError:
            print(content)
            exit()

    def close(self) -> None:
        self.client.shutdown()
        self.client.exit()


class FastLspClient(LspClient):
    def __init__(
        self,
        root_uri: str,
        timeout: int = 30,
        memory_limit: int = 80097152,
        coq_lsp: str = "coq-lsp -D 0.001",
    ):
        self.file_progress: Dict[str, List[CoqFileProgressParams]] = {}

        if sys.platform.startswith("linux"):
            command = f"ulimit -v {memory_limit}; {coq_lsp}"
        else:
            command = coq_lsp

        proc = subprocess.Popen(
            command,
            stdout=subprocess.PIPE,
            stdin=subprocess.PIPE,
            shell=True,
        )
        json_rpc_endpoint = JsonRpcEndpoint(proc.stdin, proc.stdout)
        lsp_endpoint = LspEndpoint(json_rpc_endpoint, timeout=timeout)
        # lsp_endpoint.notify_callbacks = {
        #     "$/coq/fileProgress": self.__handle_file_progress,
        #     "textDocument/publishDiagnostics": self.__handle_publish_diagnostics,
        # }

        super().__init__(lsp_endpoint)
        workspaces = [{"name": "coq-lsp", "uri": root_uri}]

        init_options = {
            "verbosity": 1,
            # "check_only_on_request": True,
        }
        self.init_options = init_options

        self.initialize(
            proc.pid,
            "",
            root_uri,
            init_options,
            {},
            "off",
            workspaces,
        )
        self.initialized()

    def didOpen(self, textDocument: TextDocumentItem):
        """Open a text document in the server.

        Args:
            textDocument (TextDocumentItem): Text document to open
        """
        self.lsp_endpoint.diagnostics[textDocument.uri] = []
        super().didOpen(textDocument)

    def didChange(
        self,
        textDocument: VersionedTextDocumentIdentifier,
        contentChanges: list[TextDocumentContentChangeEvent],
    ):
        """Submit changes on a text document already open on the server.

        Args:
            textDocument (VersionedTextDocumentIdentifier): Text document changed.
            contentChanges (list[TextDocumentContentChangeEvent]): Changes made.
        """
        self.lsp_endpoint.diagnostics[textDocument.uri] = []
        super().didChange(textDocument, contentChanges)

    def proof_goals(
        self, textDocument: TextDocumentIdentifier, position: Position
    ) -> Optional[GoalAnswer]:
        """Get proof goals and relevant information at a position.

        Args:
            textDocument (TextDocumentIdentifier): Text document to consider.
            position (Position): Position used to get the proof goals.

        Returns:
            GoalAnswer: Contains the goals at a position, messages associated
                to the position and if errors exist, the top error at the position.
        """
        result_dict = self.lsp_endpoint.call_method(
            "proof/goals",
            textDocument=textDocument,
            position=position,
        )
        parsed_goals = GoalAnswer.parse(result_dict)
        return parsed_goals

    def get_document(
        self, textDocument: TextDocumentIdentifier
    ) -> Optional[FlecheDocument]:
        """Get the AST of a text document.

        Args:
            textDocument (TextDocumentIdentifier): Text document

        Returns:
            Optional[FlecheDocument]: Serialized version of Fleche's document
        """
        result_dict = self.lsp_endpoint.call_method(
            "coq/getDocument", textDocument=textDocument
        )
        return FlecheDocument.parse(result_dict)

    def save_vo(self, textDocument: TextDocumentIdentifier):
        """Save a compiled file to disk.

        Args:
            textDocument (TextDocumentIdentifier): File to be saved.
                The uri in the textDocument should contain an absolute path.
        """
        self.lsp_endpoint.call_method("coq/saveVo", textDocument=textDocument)

    # TODO: handle performance data notification?
