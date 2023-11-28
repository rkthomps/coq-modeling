from __future__ import annotations
from typing import Any, Union

from typeguard import typechecked


@typechecked
class TrainLog:
    def __init__(
        self, epoch: float, learning_rate: float, loss: float, step: int
    ) -> None:
        assert type(epoch) == float
        assert type(learning_rate) == float
        assert type(loss) == float
        assert type(step) == int
        self.epoch = epoch
        self.learning_rate = learning_rate
        self.loss = loss
        self.step = step

    @classmethod
    def from_json(cls, json_data: Any) -> TrainLog:
        epoch = json_data["epoch"]
        learning_rate = json_data["learning_rate"]
        loss = json_data["loss"]
        step = json_data["step"]
        return cls(epoch, learning_rate, loss, step)

    @classmethod
    def steps_from_checkpoint(cls, train_state_data: Any) -> list[TrainLog]:
        steps: list[TrainLog] = []
        for step_data in train_state_data["log_history"]:
            steps.append(cls.from_json(step_data))
        return steps


class EvalLog:
    def __init__(
        self,
        epoch: float,
        eval_loss: float,
        eval_runtime: float,
        eval_samples_per_second: float,
        eval_steps_per_second: float,
        step: int,
    ) -> None:
        assert type(epoch) == float
        assert type(eval_loss) == float
        assert type(eval_runtime) == float
        assert type(eval_samples_per_second) == float
        assert type(eval_steps_per_second) == float
        assert type(step) == int
        self.epoch = epoch
        self.eval_loss = eval_loss
        self.eval_runtime = eval_runtime
        self.eval_samples_per_second = eval_samples_per_second
        self.eval_steps_per_second = eval_steps_per_second
        self.step = step

    @classmethod
    def from_json(cls, json_data: Any) -> EvalLog:
        epoch = json_data["epoch"]
        eval_loss = json_data["eval_loss"]
        eval_runtime = json_data["eval_runtime"]
        eval_samples_per_second = json_data["eval_samples_per_second"]
        eval_steps_per_second = json_data["eval_steps_per_second"]
        step = json_data["step"]
        return cls(
            epoch,
            eval_loss,
            eval_runtime,
            eval_samples_per_second,
            eval_steps_per_second,
            step,
        )


def parse_log_entry(json_data: Any) -> Union[EvalLog, TrainLog]:
    try:
        return EvalLog.from_json(json_data)
    except KeyError:
        return TrainLog.from_json(json_data)


def parse_train_longs(json_list: list[Any]) -> list[TrainLog]:
    assert type(json_list) == list
    train_logs: list[TrainLog] = []
    for entry in json_list:
        log = parse_log_entry(entry)
        if isinstance(log, TrainLog):
            train_logs.append(log)
    return train_logs


def parse_eval_logs(json_list: list[Any]) -> list[EvalLog]:
    assert type(json_list) == list
    eval_logs: list[EvalLog] = []
    for entry in json_list:
        log = parse_log_entry(entry)
        if isinstance(log, EvalLog):
            eval_logs.append(log)
    return eval_logs
