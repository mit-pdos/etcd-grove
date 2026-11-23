/-
Copied from dsverify-lab's quepaxa-bump-1 (its kit generator's lean.trusted_init; notes/dsv-quepaxa.md).

Trusted definitions of `gopkg.in/yaml.v2`, in namespace `gopkg_in.yaml_v2` like the generated package: its initialization
only. `init.0`, `_`'s initializer, `mapItemType`'s initializer, `durationType`'s initializer, `defaultMapType`'s initializer, `ifaceType`'s initializer, `timeType`'s initializer, `ptrTimeType`'s initializer, `base60float`'s initializer, `default_tag_directives`'s initializer, `resolveTable`'s initializer, `resolveMap`'s initializer, `yamlStyleFloat`'s initializer, `allowedTimestampFormats`'s initializer, `structMap`'s initializer, `eventStrings`'s initializer do nothing (goose's config for the package lists them as trusted and leaves them out of
the translation). The claim: in Go they touch no state the program reads and cannot panic (for a
`.pb.go` file: protoc-gen-go's descriptor registration, which a program without reflection does not
observe; for a names-only library: tables and settings no call of the program reaches).
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
def «_».init : val :=
  λ: <>, #()
def mapItemType.init : val :=
  λ: <>, #()
def durationType.init : val :=
  λ: <>, #()
def defaultMapType.init : val :=
  λ: <>, #()
def ifaceType.init : val :=
  λ: <>, #()
def timeType.init : val :=
  λ: <>, #()
def ptrTimeType.init : val :=
  λ: <>, #()
def base60float.init : val :=
  λ: <>, #()
def default_tag_directives.init : val :=
  λ: <>, #()
def resolveTable.init : val :=
  λ: <>, #()
def resolveMap.init : val :=
  λ: <>, #()
def yamlStyleFloat.init : val :=
  λ: <>, #()
def allowedTimestampFormats.init : val :=
  λ: <>, #()
def structMap.init : val :=
  λ: <>, #()
def eventStrings.init : val :=
  λ: <>, #()

end code
end gopkg_in.yaml_v2

end Perennial
