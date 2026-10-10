/-
The proved results of bbolt's root package: mapping and unmapping the database file
(`mmap`, `munmap`), over the file and memory-map model (`Proof/os/FileModel.lean`, whose
operations' specs are axioms). `Link.lean` links every proof to its callees' results.

`#print axioms` on a result is its trust base (`sorryAx` is unfinished work); the model's
axioms (`fileBytes`, `unix.Mmap.wp_proof`, ...) appear in it.
-/
module

public import Proof.go_etcd_io.bbolt.Link

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt

#print axioms wp_mmap
#print axioms wp_munmap

end bbolt
end EtcdGrove
end Perennial
