
## from 2a, round 1

`Grpc.addrAt ep C` is `∃ P, Http.protoAt ep (grpcOver C P)`. Two bindings of one address must agree.
2a needs a law `Http.protoAt_agree : protoAt a P ∗ protoAt a P' ⊢ ⌜P = P'⌝`, which is true since a
string's protocol is set once from its single `addrFree`.
