/-
Trusted definitions of `gopkg.in/yaml.v2`, in namespace `gopkg_in.yaml_v2` like the generated package: its
initialization only (notes/dsv-quepaxa.md; the lab's quepaxa-bump-1 made the same kind of no-op
models of its names-only packages' initializers, `lean.trusted_init`). `init.0`, `allowedTimestampFormats`, `base60float`, `defaultMapType`, `default_tag_directives`, `disableLineWrapping`, `durationType`, `eventStrings`, `ifaceType`, `mapItemType`, `ptrTimeType`, `resolveMap`, `resolveTable`, `structMap`, `timeType`, `yamlStyleFloat` do nothing
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

namespace gopkg_in.yaml_v2
section code
variable [GooseExts] [GoGlobalContext]

def init.«0».impl : val :=
  λ: <>, #()
def allowedTimestampFormats.init : val :=
  λ: <>, #()
def base60float.init : val :=
  λ: <>, #()
def defaultMapType.init : val :=
  λ: <>, #()
def default_tag_directives.init : val :=
  λ: <>, #()
def disableLineWrapping.init : val :=
  λ: <>, #()
def durationType.init : val :=
  λ: <>, #()
def eventStrings.init : val :=
  λ: <>, #()
def ifaceType.init : val :=
  λ: <>, #()
def mapItemType.init : val :=
  λ: <>, #()
def ptrTimeType.init : val :=
  λ: <>, #()
def resolveMap.init : val :=
  λ: <>, #()
def resolveTable.init : val :=
  λ: <>, #()
def structMap.init : val :=
  λ: <>, #()
def timeType.init : val :=
  λ: <>, #()
def yamlStyleFloat.init : val :=
  λ: <>, #()

end code
end gopkg_in.yaml_v2

end Perennial
