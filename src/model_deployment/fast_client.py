import sys
import threading
import subprocess
import time

from coqpyt.lsp.structs import *
from coqpyt.lsp.json_rpc_endpoint import JsonRpcEndpoint
from coqpyt.lsp.endpoint import LspEndpoint
from coqpyt.lsp.client import LspClient
from coqpyt.coq.lsp.structs import *


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

        super().__init__(lsp_endpoint)
        workspaces = [{"name": "coq-lsp", "uri": root_uri}]

        init_options = {
            "verbosity": 1,
            #"check_only_on_request": True,
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
        start = time.time()
        result_dict = self.lsp_endpoint.call_method(
            "proof/goals", textDocument=textDocument, position=position,
        )
        end = time.time()
        print('goal time str: ', end - start)
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
