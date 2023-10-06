

import argparse
import sys, os
import pdb
import shutil
import pytorch_lightning as pl
from pytorch_lightning.cli import LightningArgumentParser, LightningCLI

from premise_selection.datamodule import PremiseDataModule 
from premise_selection.model import PremiseRetriever
from data_management.create_premise_dataset import PREMISE_DATA_CONF_NAME


class CLI(LightningCLI):
    def add_arguments_to_parser(self, parser: LightningArgumentParser) -> None:
        parser.link_arguments("trainer.max_steps", "model.max_steps")
        parser.link_arguments("model.model_name", "data.model_name") 
        parser.link_arguments("data.max_seq_len", "model.max_seq_len")

    def before_fit(self) -> None:
        subcommand = self.config["subcommand"]
        subconfig = self.config[subcommand]
        premise_data_path = subconfig["data"]["premise_data_path"]
        data_conf_loc = os.path.join(premise_data_path, PREMISE_DATA_CONF_NAME)
        output_path = subconfig["trainer"]["default_root_dir"]
        os.makedirs(output_path)
        shutil.copy(data_conf_loc, os.path.join(output_path, PREMISE_DATA_CONF_NAME))


def main() -> None:
    cli = CLI(PremiseRetriever, PremiseDataModule)


if __name__ == "__main__":
    main()





