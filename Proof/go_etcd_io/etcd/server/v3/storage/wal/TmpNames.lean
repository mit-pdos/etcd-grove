/- Lean-first (no Rocq counterpart).

# The file pipeline's names (unit `locks`, session 10)

`walTmps`, the names the WAL's file pipeline creates in the WAL directory, on their own so that the ghost
layer (`Ghost.lean`: a directory key says its claim leaves out exactly these names, `walDirKey`) and the
layout layer (`Cut.lean`) both state facts of them.
-/
module

public import Perennial.Std.ByteString

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace WalFs

/-- The file pipeline's names (`fmt.Sprintf("%d.tmp", fp.count%2)`, file_pipeline.go:77). -/
def walTmps : List GoString := [go!"0.tmp", go!"1.tmp"]

end WalFs
end EtcdGrove
end Perennial

end
