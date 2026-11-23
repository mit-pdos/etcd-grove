/-
Trusted definitions of `google.golang.org/grpc`, in namespace `google_golang_org.grpc` like the generated package: its
initialization only (notes/dsv-quepaxa.md; the lab's quepaxa-bump-1 made the same kind of no-op
models of its names-only packages' initializers, `lean.trusted_init`). `init.0`, `init.1`, `init.2`, `DefaultBackoffConfig`, `ErrClientConnClosing`, `ErrClientConnTimeout`, `ErrServerStopped`, `PickFirstBalancerName`, `defaultServerOptions`, `emptyMethodConfig`, `errConnClosing`, `errConnDrain`, `errConnIdling`, `errContextCanceled`, `errContextDeadline`, `errIllegalHeaderWrite`, `errMalformedFrame`, `errNoTransportCredsInBundle`, `errNoTransportSecurity`, `errStreamDone`, `errTransportClosing`, `errTransportCredentialsMissing`, `errTransportCredsAndBundle`, `grpcStatusDetailsBinHeader`, `http2ErrCodeNames`, `http2ErrConvTab`, `invalidDefaultServiceConfigErrPrefix`, `logger`, `metadataFromOutgoingContextRaw`, `modelChooseRandom`, `statusOK`, `transportFailureCodes`, `unaryStreamDesc`, `_` do nothing
(the package's goose config lists them as trusted and leaves them out of the translation). The
claim: the package is translated names only, no call of the verified program reaches it except
through calls whose specs are hypotheses of the port, so its initialization's tables and settings
are not observed by anything proved.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace google_golang_org.grpc
section code
variable [GooseExts] [GoGlobalContext]

def init.«0».impl : val :=
  λ: <>, #()
def init.«1».impl : val :=
  λ: <>, #()
def init.«2».impl : val :=
  λ: <>, #()
def DefaultBackoffConfig.init : val :=
  λ: <>, #()
def ErrClientConnClosing.init : val :=
  λ: <>, #()
def ErrClientConnTimeout.init : val :=
  λ: <>, #()
def ErrServerStopped.init : val :=
  λ: <>, #()
def PickFirstBalancerName.init : val :=
  λ: <>, #()
def defaultServerOptions.init : val :=
  λ: <>, #()
def emptyMethodConfig.init : val :=
  λ: <>, #()
def errConnClosing.init : val :=
  λ: <>, #()
def errConnDrain.init : val :=
  λ: <>, #()
def errConnIdling.init : val :=
  λ: <>, #()
def errContextCanceled.init : val :=
  λ: <>, #()
def errContextDeadline.init : val :=
  λ: <>, #()
def errIllegalHeaderWrite.init : val :=
  λ: <>, #()
def errMalformedFrame.init : val :=
  λ: <>, #()
def errNoTransportCredsInBundle.init : val :=
  λ: <>, #()
def errNoTransportSecurity.init : val :=
  λ: <>, #()
def errStreamDone.init : val :=
  λ: <>, #()
def errTransportClosing.init : val :=
  λ: <>, #()
def errTransportCredentialsMissing.init : val :=
  λ: <>, #()
def errTransportCredsAndBundle.init : val :=
  λ: <>, #()
def grpcStatusDetailsBinHeader.init : val :=
  λ: <>, #()
def http2ErrCodeNames.init : val :=
  λ: <>, #()
def http2ErrConvTab.init : val :=
  λ: <>, #()
def invalidDefaultServiceConfigErrPrefix.init : val :=
  λ: <>, #()
def logger.init : val :=
  λ: <>, #()
def metadataFromOutgoingContextRaw.init : val :=
  λ: <>, #()
def modelChooseRandom.init : val :=
  λ: <>, #()
def statusOK.init : val :=
  λ: <>, #()
def transportFailureCodes.init : val :=
  λ: <>, #()
def unaryStreamDesc.init : val :=
  λ: <>, #()
def «_».init : val :=
  λ: <>, #()

end code
end google_golang_org.grpc

end Perennial
