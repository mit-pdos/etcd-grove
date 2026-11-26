"""(option (b)) StepEnd's gated arm takes `¬ XtRec id m s`: append `(by xtrec_tac)` to each reader's
application of a `StepEnd` hypothesis to its type fact."""
import re, sys
pats = [
  (r"\((hend|h|Hend) (hty|hety|hte)\)", r"(\1 \2 (by xtrec_tac))"),
  (r":= h hT$", r":= h hT (by xtrec_tac)"),
  (r"hst \(h hT\)$", r"hst (h hT (by xtrec_tac))"),
  (r":= h \(by unfold StepEndTy; (ie|se)_tyclose hty\)$", r":= h (by unfold StepEndTy; \1_tyclose hty) (by xtrec_tac)"),
  (r"\(h \(by unfold StepEndTy; ie_tyclose hty\)\)$", r"(h (by unfold StepEndTy; ie_tyclose hty) (by xtrec_tac))"),
]
for p in sys.argv[1:]:
    s = open(p).read(); o = s
    for a, b in pats:
        s = re.sub(a, b, s, flags=re.M)
    if s != o:
        open(p, 'w').write(s); print("rewrote", p, sum(1 for x,y in zip(o.splitlines(), s.splitlines()) if x!=y))
