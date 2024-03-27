from parsy import regex, string, any_char, eof, seq, ParseError
import ipdb

_open_commentp = string("(*")
_close_commentp = string("*)")
_commentp = (
    _open_commentp + any_char.until(_close_commentp, consume_other=True).concat()
)

_quotep = string('"')
_stringp = _quotep + any_char.until(_quotep, consume_other=True).concat()

_period_end = regex(r"\.(?=\s|$)")
_focus_tok = regex(r"\s[-+*]+(?=\s|$)")
_bracket_open = regex(r"\s+{(?=\s)|$")

_bracket_close = regex(r"\s}(?=\s|$)")
_focus_end = _focus_tok | _bracket_open | _bracket_close

_end_stepp = _period_end | _focus_end

_step2cmtp = any_char.until(_open_commentp, min=1).concat() + _commentp.concat()
_step2strp = any_char.until(_quotep, min=1).concat() + _stringp.concat()
_step2endp = any_char.until(_end_stepp, consume_other=True, min=1).concat()

_step_w_otherp = (_step2cmtp | _step2strp).at_least(1).concat() + _step2endp
_stepp = _step2endp | _step_w_otherp

_whitespacep = regex(r"\s")
_proofp = _stepp.many() << _whitespacep.many()


def separate_steps(step_str: str) -> list[str]:
    return _proofp.parse(step_str)
    # try:
    # except ParseError:
    #     ipdb.set_trace()


if __name__ == "__main__":
    print(separate_steps("intros. induction n."))
