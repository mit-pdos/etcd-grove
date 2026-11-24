/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/Valid.lean (lab master 915f964;
notes/dsv-vr.md): `jsonValid` is `models_lab.jsoncodec.jsonValid` (its whitespace `spaceB`, the
lab's `isSpaceB`: `encoding.json.isSpaceB_spaceB`).
-/
/-
Validity (`models_lab.jsoncodec.jsonValid`) of the kit's encodings by the Lean scanner.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.jsonlib
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Frame

@[expose] public section

namespace VsrJson

open JsonScan

open Perennial VsrModel

theorem isSpaceB_spB (c : w8) : encoding.json.isSpaceB c = spB c := by
  simp [encoding.json.isSpaceB, spB]

/-- A whole value (not a number) after whitespace is valid JSON, when it fits a word. -/
theorem valid_value (ws : List w8) (v : JV) (hv : v.ok) (hd : v.depth ≤ maxDepth)
    (ht : termOK v []) (hws : ∀ c ∈ ws, encoding.json.isSpaceB c = true)
    (hlen : (ws ++ ser v).length < 2 ^ 64) :
    models_lab.jsoncodec.jsonValid scanF (ws ++ ser v) := by
  have hsp : ∀ c ∈ ws, spB c = true := fun c hc => by
    rw [← isSpaceB_spB]; exact hws c hc
  have e := scanL_value ws v hv hd hsp ht
  simp only [List.length_append] at hlen
  have hn : uint.nat (W64 ((ws.length + (ser v).length : Nat) : Int)) =
      ws.length + (ser v).length := by
    simp only [uint.nat, W64]; rw [BitVec.toNat_ofInt]; omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [scanF, e]; rfl
  · simp only [scanF, e, hn, List.length_append]; omega
  · simp only [scanF, e, hn]
    intro c hc
    rw [List.drop_eq_nil_of_le (by simp)] at hc
    simp at hc

theorem logsJV_maxd (es : List Entry) : (logsJV es).depth ≤ maxDepth := by
  have := logsJV_depth es; simp only [maxDepth]; omega

theorem payJV_maxd (m : Msg) : (payJV m).depth ≤ maxDepth := by
  have := payJV_depth m; simp only [maxDepth]; omega

theorem payJV_obj (m : Msg) : ∃ ms, payJV m = .obj ms := by
  cases m <;> simp [payJV, reqJV]

end VsrJson
