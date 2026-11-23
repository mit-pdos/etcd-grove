/-
Copied from dsverify-lab's quepaxa-bump-1 (its kit generator's lean.trusted_init; notes/dsv-quepaxa.md).

Trusted definitions of `raxos/proto/client`, in namespace `raxos.proto.client` like the generated package: its initialization
only. `init.0`, `file_proto_client_client_proto_rawDesc`'s initializer, `file_proto_client_client_proto_rawDescData`'s initializer, `file_proto_client_client_proto_msgTypes`'s initializer, `file_proto_client_client_proto_goTypes`'s initializer, `file_proto_client_client_proto_depIdxs`'s initializer do nothing (goose's config for the package lists them as trusted and leaves them out of
the translation). The claim: in Go they touch no state the program reads and cannot panic (for a
`.pb.go` file: protoc-gen-go's descriptor registration, which a program without reflection does not
observe; for a names-only library: tables and settings no call of the program reaches).
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace raxos.proto.client
section code
variable [GooseExts] [GoGlobalContext]

def init.«0».impl : val :=
  λ: <>, #()
def file_proto_client_client_proto_rawDesc.init : val :=
  λ: <>, #()
def file_proto_client_client_proto_rawDescData.init : val :=
  λ: <>, #()
def file_proto_client_client_proto_msgTypes.init : val :=
  λ: <>, #()
def file_proto_client_client_proto_goTypes.init : val :=
  λ: <>, #()
def file_proto_client_client_proto_depIdxs.init : val :=
  λ: <>, #()

end code
end raxos.proto.client

end Perennial
