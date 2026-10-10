/-
The proved results of bbolt's `internal/common` (the page-id helpers, the only part of bbolt
that is goosable as written: `notes/bbolt-unsafe.md`). `Mergepgids` has no callees of its own
package (it calls Perennial's `sort.Search`), so its proof needs no linking.

`#print axioms` on a result is its trust base (`sorryAx` is unfinished work).
-/
module

public import Proof.go_etcd_io.bbolt.internal.common.Mergepgids

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt

#print axioms Mergepgids.wp_proof

end bbolt
end EtcdGrove
end Perennial
