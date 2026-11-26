/-
`op(s, c, in)` (`kit.go`), client `c`'s operation on its node, over remote's update (the lab's
`ClientOp.lean`, whose operation was logically atomic over the lab driver's update, redone for the
kit over remote): under `opMu` (`opInv`), `op1` answers unknown past `MaxOps` operations or for a
value of `MaxVal` bytes or more; otherwise it counts the operation, connects at the first
operation (or after a failed connect: an unknown outcome, the client still unconnected), then
`BufferClient.Write` (a put) or `Read` (a get), whose logically atomic triples commit remote's
update through the link invariant (`ClientLin.lean`'s `put_of_lin`, `get_of_lin`). Also
`returned`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeDefs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.imdea_software.swiftpaxos.examples.swiftnet

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

section calls
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [ρ : RemoteGS]

/-- A slot's update gives its `lin` (a read's persistently). -/
theorem slotUpd_lin {St J I O : Type} (R : RBase netDistGF St J I O) (i : I) (Φ : O → IProp netDistGF) :
    slotUpd (Gg := hG.goose_globalGS) R i Φ ⊢ lin (Gg := hG.goose_globalGS) R i Φ := by
  unfold slotUpd
  split
  · exact .rfl
  · exact BI.intuitionistically_elim

/-- `b.Write(key, vsl)` for a put `i`, with remote's update: committed at the triple's
commit, the client ready at `sq + 1`. -/
theorem wp_put (wp_Write : client.BufferClient.Write.spec) (γ : SwiftNames netDistGF) (γk : GName)
    (b : Loc) (cid : w32) (sq : Nat) (i : KIn) (hput : i.put = true) (vsl : GoSlice)
    (hlen : i.val.length < 2 ^ 16) (hs : sq < 2 ^ 10) (Q : BStr → IProp netDistGF) :
    ⊢ ∀ Ψ : val → IProp netDistGF,
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
        client.ready b γ.sp γ.conf γ.mem γ.lin cid sq ∗ vsl ↦*□ i.val ∗
        linkInv (G := hG.goose_globalGS) γ γk ∗ lin (Gg := hG.goose_globalGS) (swRK γk) i Q -∗
      (client.ready b γ.sp γ.conf γ.mem γ.lin cid (sq + 1) -∗ Q bnil -∗ Ψ #()) -∗
      WP (App (App (Val (b @!! go.GoType.PointerType client.BufferClient.ty @!! go!"Write"))
        (Val #(W64 (i.key : Int)))) (Val #vsl)) {{ Ψ }} := by
  iintro %Ψ ⟨#Hpkg, Hready, #Hv, #Hinv, Hlin⟩ HΨ
  ihave Hw := wp_Write b γ.sp γ.conf γ.mem γ.lin cid sq (W64 (i.key : Int)) vsl i.val
    $$ Hpkg Hready Hv %(And.intro hlen hs)
  ihave Hwp := put_of_lin γ γk i hput Q _ _ $$ Hw Hinv Hlin
  iapply wp_wand $$ Hwp
  iintro %r ⟨%Hr, HP, HQ⟩
  subst Hr
  iapply HΨ $$ HP HQ

/-- `b.Read(key)` for a get `i`, with remote's update: committed at the triple's commit, the
returned slice holding the output's bytes. -/
theorem wp_get (wp_Read : client.BufferClient.Read.spec) (γ : SwiftNames netDistGF) (γk : GName)
    (b : Loc) (cid : w32) (sq : Nat) (i : KIn) (hget : i.put = false)
    (hs : sq < 2 ^ 10) (Q : BStr → IProp netDistGF) :
    ⊢ ∀ Ψ : val → IProp netDistGF,
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
        client.ready b γ.sp γ.conf γ.mem γ.lin cid sq ∗
        linkInv (G := hG.goose_globalGS) γ γk ∗ lin (Gg := hG.goose_globalGS) (swRK γk) i Q -∗
      (∀ (sl : GoSlice) (o : BStr), sl ↦*□ o.1 -∗
        client.ready b γ.sp γ.conf γ.mem γ.lin cid (sq + 1) -∗ Q o -∗ Ψ #sl) -∗
      WP (App (Val (b @!! go.GoType.PointerType client.BufferClient.ty @!! go!"Read"))
        (Val #(W64 (i.key : Int)))) {{ Ψ }} := by
  iintro %Ψ ⟨#Hpkg, Hready, #Hinv, Hlin⟩ HΨ
  ihave Hw := wp_Read b γ.sp γ.conf γ.mem γ.lin cid sq (W64 (i.key : Int)) $$ Hpkg Hready %hs
  ihave Hwp := get_of_lin γ γk i hget Q _ _ $$ Hw Hinv Hlin
  iapply wp_wand $$ Hwp
  iintro %r ⟨%sl, %o, %Hr, #Hsl, HP, HQ⟩
  subst Hr
  iapply HΨ $$ %sl %o Hsl HP HQ

end calls

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
  [net.http.Assumptions] [client.Assumptions] [examples.swiftnet.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]
variable [ρ : RemoteGS]

set_option goose.wp.extras true

/-- `s.returned()`. -/
theorem Sys.returned.wp_proof (γ : SwiftNames netDistGF) (c : Nat) (s : Loc) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
      isSysL γ c s }}
    (App (Val (s @!! go.GoType.PointerType examples.swiftnet.Sys.ty @!! go!"returned")) (Val #()))
  {{ RET #(); True }} := by
  wp_start as #Hs
  iunfold isSysL at Hs
  icases Hs with ⟨%conf, %asl, -, -, -, -, #Hmu, -⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  icases HR with ⟨%d, Hd⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hd]
  · iframe Hmu Hlocked
    iexists _
    iexact Hd
  iapply HΦ $$ %trivial

/-- `op1(s, c, in)`, with `opMu` held: see the file header. -/
theorem op1.wp_proof (γ : SwiftNames netDistGF) (γk : GName) (c : Nat)
    (wp_connect : Sys.connect.spec γ c)
    (wp_Write : client.BufferClient.Write.spec) (wp_Read : client.BufferClient.Read.spec)
    (s : Loc) (i : KIn) (Q : BStr → IProp netDistGF) (j : w64) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
        isSysL γ c s ∗ linkInv (G := hG.goose_globalGS) γ γk ∗
        slotUpd (Gg := hG.goose_globalGS) (swRK (G := hG.goose_globalGS) γk) i Q ∗
        s.[examples.swiftnet.Sys, go!"ops"] ↦ j ∗ ⌜uint.nat j ≤ maxOps⌝ ∗ clSt γ s c (uint.nat j) }}
      (App (App (App (Val (@! examples.swiftnet.op1)) (Val #s)) (Val #(W64 (c : Int))))
        (Val #(inVal i)))
    {{ (o : examples.swiftnet.Out), RET #o; opInv γ s c ∗ (⌜o = Out.mk true []⌝ ∨
        ∃ w : BStr, ⌜o = Out.mk false w.1⌝ ∗ Q w) }} := by
  wp_start as ⟨#Hs, #Hinv, Hupd, Hops, %Hj, Hst⟩
  ihave #Hcpkg : isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
  · iPkgInit
  ihave HU := slotUpd_lin _ i Q $$ Hupd
  wp_auto
  wp_if_destruct
  · -- past `MaxOps`
    try wp_auto
    iapply HΦ
    isplitl [Hops Hst]
    · iunfold opInv; iexists j; iframe; ipureintro; exact Hj
    ileft; ipureintro; rfl
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl63
  try wp_auto
  wp_if_destruct
  · -- a value too long
    try wp_auto
    iapply HΦ
    isplitl [Hops Hst]
    · iunfold opInv; iexists j; iframe; ipureintro; exact Hj
    ileft; ipureintro; rfl
  have hj : uint.nat j < maxOps := by unfold maxOps; word
  have hvl : i.val.length < 2 ^ 16 := by
    have h48 : i.val.length < 2 ^ 48 := i.2.2
    word
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ c_ptr ↦ W64 (c : Int) ∗ s_ptr ↦ s ∗ in_ptr ↦ inVal i ∗
        «$res0_ptr» ↦ zero_val examples.swiftnet.Out ∗ ∃ (b : Loc) (sq : Nat),
        s.[examples.swiftnet.Sys, go!"b"] ↦ b ∗ ⌜b ≠ null ∧ sq ≤ uint.nat j⌝ ∗
        client.ready b γ.sp γ.conf γ.mem γ.lin (cidOf c) sq) ∨
      (⌜v = returnVal #()⌝ ∗ «$res0_ptr» ↦ Out.mk true [] ∗
        clSt γ s c (uint.nat j + 1))))
    at next with [Hst c s «in» «$res0»]
  · iunfold clSt at Hst
    icases Hst with (⟨Hb, Hseq⟩ | ⟨%b, %sq, Hb, %Hbs, Hready⟩)
    · wp_auto
      wp_apply wp_connect s $$ [Hb Hseq] as %ok Hok
      · iframe Hs Hb Hseq
      cases ok
      · simp only [Bool.false_eq_true, ↓reduceIte]
        wp_auto
        iright
        iframe
        isplitr
        · ipureintro; rfl
        iunfold clSt
        ileft
        iexact Hok
      · simp only [↓reduceIte]
        wp_auto
        ileft
        iframe
        isplitr
        · ipureintro; rfl
        icases Hok with ⟨%b, Hb, %Hb, Hready⟩
        iexists b, 0
        iframe
        ipureintro; exact ⟨Hb, Nat.zero_le _⟩
    · wp_auto
      wp_if_destruct
      · exact absurd rfl Hbs.1
      ileft
      iframe
      ipureintro
      first | exact Hbs | exact ⟨rfl, Hbs⟩
  iintro (⟨%Hv, c, s, «in», «$res0», %b, %sq, Hb, %Hbs, Hready⟩ | ⟨%Hv, «$res0», Hst⟩)
  rotate_left
  · subst Hv
    wp_auto
    iapply HΦ
    isplitl [Hops Hst]
    · iunfold opInv
      iexists j + W64 1
      have hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by unfold maxOps at hj; word
      rw [hj1]
      iframe
      ipureintro; unfold maxOps at hj ⊢; omega
    ileft; ipureintro; rfl
  subst Hv
  have hsq : sq < 2 ^ 10 := by unfold maxOps at hj; omega
  have hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by unfold maxOps at hj; word
  wp_auto
  cases hp : i.put
  · -- a get
    simp only [inVal, hp]
    wp_auto
    wp_apply wp_get wp_Read γ γk b (cidOf c) sq i hp hsq Q $$ [$Hready $HU] as %sl %o #Hsl Hready HΦo
    · iframe #
    wp_apply Sys.returned.wp_proof γ c s $$ []
    · iframe #
    wp_apply wp_bytes_to_string sl o.1 _ $$ [] as -
    · iexact Hsl
    try wp_auto
    iapply HΦ
    isplitl [Hops Hb Hready]
    · iunfold opInv
      iexists j + W64 1
      rw [hj1]
      iframe
      isplitr
      · ipureintro; unfold maxOps at hj ⊢; omega
      iunfold clSt
      iright
      iexists b, sq + 1
      iframe
      ipureintro; exact ⟨Hbs.1, by omega⟩
    iright
    iexists o
    iframe
    ipureintro; rfl
  · -- a put
    simp only [inVal, hp]
    wp_auto
    wp_apply wp_string_to_bytes i.val as %vsl ⟨Hvsl, -⟩
    imod ownSlice_persist $$ Hvsl with #Hvsl
    wp_apply wp_put wp_Write γ γk b (cidOf c) sq i hp vsl hvl hsq Q $$ [$Hready $HU] as Hready HΦo
    · iframe #
    wp_apply Sys.returned.wp_proof γ c s $$ []
    · iframe #
    try wp_auto
    iapply HΦ
    isplitl [Hops Hb Hready]
    · iunfold opInv
      iexists j + W64 1
      rw [hj1]
      iframe
      isplitr
      · ipureintro; unfold maxOps at hj ⊢; omega
      iunfold clSt
      iright
      iexists b, sq + 1
      iframe
      ipureintro; exact ⟨Hbs.1, by omega⟩
    iright
    iexists bnil
    iframe
    ipureintro; rfl

/-- `op(s, c, in)`: `op1` under `opMu`. -/
theorem op.wp_proof (γ : SwiftNames netDistGF) (γk : GName) (c : Nat)
    (wp_connect : Sys.connect.spec γ c)
    (wp_Write : client.BufferClient.Write.spec) (wp_Read : client.BufferClient.Read.spec) :
    op.spec γ γk c := by
  intro s i Ψ
  wp_start as ⟨#Hs, #Hinv, Hupd⟩
  ihave #Hs' := Hs
  iunfold isSysL at Hs'
  icases Hs' with ⟨%conf, %asl, -, -, -, -, -, #Hopmu, -⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hopmu
  iunfold opInv at HR
  icases HR with ⟨%j, Hops, %Hj, Hst⟩
  wp_auto
  wp_apply op1.wp_proof γ γk c wp_connect wp_Write wp_Read s i Ψ j $$ [$Hops $Hst $Hupd]
    as %o ⟨HI, Ho⟩
  · iframe #; ipureintro; exact Hj
  wp_apply sync.Mutex.wp_Unlock $$ [Hlocked HI]
  · iframe Hopmu Hlocked HI
  try wp_auto
  iapply HΦ $$ Ho

end proof

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
