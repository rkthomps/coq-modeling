

from pytorch_lightning.cli import LightningArgumentParser, LightningCLI

from premise_selection.datamodule import PremiseDataModule 
from premise_selection.model import PremiseRetriever

class CLI(LightningCLI):
    def add_arguments_to_parser(self, parser: LightningArgumentParser) -> None:
        parser.link_arguments("trainer.max_steps", "model.max_steps")
        parser.link_arguments("model.model_name", "data.model_name") 
        parser.link_arguments("data.max_seq_len", "model.max_seq_len")


def main() -> None:
    cli = CLI(PremiseRetriever, PremiseDataModule)


if __name__ == "__main__":
    main()




