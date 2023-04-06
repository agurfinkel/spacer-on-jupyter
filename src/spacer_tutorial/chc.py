"""CHC utility function."""

import z3


class HtmlStr(object):
    """Converts an object to HTML string."""

    def __init__(self, s):
        """init."""
        self._s = str(s)
        self._s = self._s.replace('\n', '<br/>')

    def _repr_html_(self):
        return self._s

    def __repr__(self):
        return repr(self._s)

    def __str__(self):
        return str(self._s)

def chc_to_str(chc):
    """Convert CHC to appropriate string."""
    if z3.in_html_mode():
        return chc_to_html(chc)
    else:
        return chc_to_txt(chc)

def chc_to_html(chc):
    """Convert CHC to HTML."""
    import io
    out = io.StringIO()

    for cls in chc:
        print(cls, '<br/>', file=out)

    return HtmlStr(out.getvalue())

def chc_to_txt(chc):
    """Convert CHC to text."""
    import io
    out = io.StringIO()
    for cls in chc:
        print(cls, file=out)
    return out.getvalue()
