(** * [math/big.Int], abstractly

    [lockedRand.Intn] -- the RNG behind [raft.resetRandomizedElectionTimeout]
    -- goes through [math/big]: [big.NewInt(int64(n))] builds the bound,
    [crypto/rand.Int] returns a [*big.Int] below it, and [big.Int.Int64]
    reads the result back.  None of that is raft code, none of it is
    translated ([new/code/math/big.v] declares [big.Int.t] as an [Axiom Type]
    and [NewInt] as a bare name; [Int64] is not even declared), and none of it
    is in scope: the RNG is on the declared trust boundary
    (notes/STATUS.md, "Trust base").

    So this file states the one abstraction the three assumed triples share.
    It is the same shape as [own_Storage] in [inv_storage.v]: **the whole
    trust surface of this file is one line**, the abstract predicate below,
    and the triples that consume it live in their own collections
    ([spec_big_NewInt.v], [spec_rand_Int.v], [spec_big_Int__Int64.v]). *)

Require Export New.proof.go_etcd_io.raft.election_proof.defs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** [own_big_Int p z]: the [big.Int] at [p] has value [z].  Abstract, because
    the representation is not translated; exclusive (not persistent), because
    a [big.Int] is mutable in Go ([Set], [Add], … write through the pointer),
    so two values for one [p] must not be simultaneously assertable. *)
Axiom own_big_Int : loc → Z → iProp Σ.

End proof.
