/-
Trusted definitions of `encoding/gob`, in namespace `encoding.gob` like the generated package: its
initialization only (notes/dsv-quepaxa.md; the lab's quepaxa-bump-1 made the same kind of no-op
models of its names-only packages' initializers, `lean.trusted_init`). `init.0`, `init.1`, `init.2`, `binaryMarshalerInterfaceType`, `binaryUnmarshalerInterfaceType`, `decArrayHelper`, `decIgnoreOpMap`, `decOpTable`, `decSliceHelper`, `emptyStructType`, `encArrayHelper`, `encBufferPool`, `encOpTable`, `encSliceHelper`, `errBadCount`, `errBadType`, `errBadUint`, `errRange`, `gobDecoderInterfaceType`, `gobEncoderInterfaceType`, `idToTypeSlice`, `maxIgnoreNestingDepth`, `spaceForLength`, `tBool`, `tBytes`, `tComplex`, `tFloat`, `tInt`, `tInterface`, `tReserved1`, `tReserved2`, `tReserved3`, `tReserved4`, `tReserved5`, `tReserved6`, `tReserved7`, `tString`, `tUint`, `tWireType`, `textMarshalerInterfaceType`, `textUnmarshalerInterfaceType`, `typeInfoMapInit`, `types`, `wireTypeType` do nothing
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

namespace encoding.gob
section code
variable [GooseExts] [GoGlobalContext]

def init.«0».impl : val :=
  λ: <>, #()
def init.«1».impl : val :=
  λ: <>, #()
def init.«2».impl : val :=
  λ: <>, #()
def binaryMarshalerInterfaceType.init : val :=
  λ: <>, #()
def binaryUnmarshalerInterfaceType.init : val :=
  λ: <>, #()
def decArrayHelper.init : val :=
  λ: <>, #()
def decIgnoreOpMap.init : val :=
  λ: <>, #()
def decOpTable.init : val :=
  λ: <>, #()
def decSliceHelper.init : val :=
  λ: <>, #()
def emptyStructType.init : val :=
  λ: <>, #()
def encArrayHelper.init : val :=
  λ: <>, #()
def encBufferPool.init : val :=
  λ: <>, #()
def encOpTable.init : val :=
  λ: <>, #()
def encSliceHelper.init : val :=
  λ: <>, #()
def errBadCount.init : val :=
  λ: <>, #()
def errBadType.init : val :=
  λ: <>, #()
def errBadUint.init : val :=
  λ: <>, #()
def errRange.init : val :=
  λ: <>, #()
def gobDecoderInterfaceType.init : val :=
  λ: <>, #()
def gobEncoderInterfaceType.init : val :=
  λ: <>, #()
def idToTypeSlice.init : val :=
  λ: <>, #()
def maxIgnoreNestingDepth.init : val :=
  λ: <>, #()
def spaceForLength.init : val :=
  λ: <>, #()
def tBool.init : val :=
  λ: <>, #()
def tBytes.init : val :=
  λ: <>, #()
def tComplex.init : val :=
  λ: <>, #()
def tFloat.init : val :=
  λ: <>, #()
def tInt.init : val :=
  λ: <>, #()
def tInterface.init : val :=
  λ: <>, #()
def tReserved1.init : val :=
  λ: <>, #()
def tReserved2.init : val :=
  λ: <>, #()
def tReserved3.init : val :=
  λ: <>, #()
def tReserved4.init : val :=
  λ: <>, #()
def tReserved5.init : val :=
  λ: <>, #()
def tReserved6.init : val :=
  λ: <>, #()
def tReserved7.init : val :=
  λ: <>, #()
def tString.init : val :=
  λ: <>, #()
def tUint.init : val :=
  λ: <>, #()
def tWireType.init : val :=
  λ: <>, #()
def textMarshalerInterfaceType.init : val :=
  λ: <>, #()
def textUnmarshalerInterfaceType.init : val :=
  λ: <>, #()
def typeInfoMapInit.init : val :=
  λ: <>, #()
def types.init : val :=
  λ: <>, #()
def wireTypeType.init : val :=
  λ: <>, #()

end code
end encoding.gob

end Perennial
