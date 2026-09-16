"""Separate Lean comments from code for source-preservation audits.

This is an audit aid, not a Lean parser or a replacement for kernel checking.
Nested comments and ordinary quoted strings are handled explicitly, so rewriting
documentation cannot accidentally be mistaken for changing a proof or definition.
"""


def segments(text):
    """Yield (is_comment, text) segments, retaining every character in order."""
    i = start = 0
    quoted = False
    while i < len(text):
        if quoted:
            if text[i] == "\\":
                i += 2
                continue
            if text[i] == '"':
                quoted = False
            i += 1
            continue
        if text[i] == '"':
            quoted = True
            i += 1
            continue
        if text.startswith("--", i) or text.startswith("/-", i):
            yield False, text[start:i]
            begin = i
            if text.startswith("--", i):
                end = text.find("\n", i)
                i = len(text) if end == -1 else end
            else:
                i += 2
                depth = 1
                while i < len(text) and depth:
                    if text.startswith("/-", i):
                        depth += 1
                        i += 2
                    elif text.startswith("-/", i):
                        depth -= 1
                        i += 2
                    else:
                        i += 1
                if depth:
                    raise ValueError("Unclosed Lean block comment")
            yield True, text[begin:i]
            start = i
        else:
            i += 1
    if quoted:
        raise ValueError("Unclosed Lean quoted string")
    yield False, text[start:]


def code_text(text):
    """Retain exact noncomment text, inserting a space for each comment."""
    return "".join(" " if comment else body for comment, body in segments(text))


def transform_comments(text, transform):
    result = "".join(transform(body) if comment else body
                     for comment, body in segments(text))
    assert code_text(result) == code_text(text), "Noncomment source changed"
    return result
