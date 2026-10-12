/-
The platform: Linux. Perennial's translation of `runtime` leaves `runtime.GOOS` an axiomatized
value, so a comparison with `"windows"` (bbolt's `grow`, `mmap`, `allocate`) cannot be
evaluated; `GOOSLinux` says what it is, taken as an instance hypothesis (Goose's
`translate_consts` for `runtime` would make it a definition).
-/
module

public import GeneratedProof.go_etcd_io.bbolt

@[expose] public section

namespace Perennial
namespace EtcdGrove

class GOOSLinux [FfiSyntax] [GoGlobalContext] : Prop where
  goos : _root_.Perennial.runtime.GOOS = #(go!"linux")

end EtcdGrove
end Perennial
