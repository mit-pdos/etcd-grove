/-
The generic set of apimachinery (`k8s.io/apimachinery/pkg/util/sets`, `set.go`): a `Set[T]` is a
`map[T]Empty`, owned as a map points-to `m ↦$ s` (`s : GMap K Elem`). What `Insert` and `Delete`
of several items do (`insertAll`, `deleteAll`). Lean-first; for client-go's work queue
(`Proof/k8s_io/client_go/util/workqueue/`).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.util.sets
public import Proof.k8s_io.apimachinery.pkg.util.sets.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

/-- The sets' element value, `Empty` (`struct{}`). -/
abbrev Elem [GooseExts] : Type := k8s_io.apimachinery.pkg.util.sets.Empty

/-- The element. -/
abbrev present [GooseExts] : Elem := ⟨⟩

/-- `Elem` is countable (for ghost maps with its values, the work queue's). -/
instance elem_countable [GooseExts] : Pos.Countable Elem :=
  .ofInjective (fun _ => Pos.Countable.encode ()) (by rintro ⟨⟩ ⟨⟩ _; rfl)

section defs
variable [GooseExts] {K : Type} [DecidableEq K]

/-- `s.Insert(ks...)`: each of `ks` in the set. -/
def insertAll (s : GMap K Elem) (ks : List K) : GMap K Elem :=
  ks.foldl (fun s k => <[k := present]> s) s

/-- `s.Delete(ks...)`: none of `ks` in the set. -/
def deleteAll (s : GMap K Elem) (ks : List K) : GMap K Elem :=
  ks.foldl (fun s k => GMap.delete k s) s

@[simp] theorem insertAll_nil (s : GMap K Elem) : insertAll s [] = s := rfl
@[simp] theorem insertAll_cons (s : GMap K Elem) (k : K) (ks : List K) :
    insertAll s (k :: ks) = insertAll (<[k := present]> s) ks := rfl
@[simp] theorem deleteAll_nil (s : GMap K Elem) : deleteAll s [] = s := rfl
@[simp] theorem deleteAll_cons (s : GMap K Elem) (k : K) (ks : List K) :
    deleteAll s (k :: ks) = deleteAll (GMap.delete k s) ks := rfl

theorem insertAll_append (s : GMap K Elem) (ks ks' : List K) :
    insertAll s (ks ++ ks') = insertAll (insertAll s ks) ks' := by
  unfold insertAll; rw [List.foldl_append]

theorem deleteAll_append (s : GMap K Elem) (ks ks' : List K) :
    deleteAll s (ks ++ ks') = deleteAll (deleteAll s ks) ks' := by
  unfold deleteAll; rw [List.foldl_append]

end defs

end sets
end EtcdGrove
end Perennial
