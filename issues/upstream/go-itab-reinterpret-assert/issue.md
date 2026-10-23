Title: cmd/compile: x.(T) and == fail on an interface value read through a *I1 to *I2 conversion

### Go version

go version go1.27.3 linux/amd64 (the same with go1.26.0, go1.27.1 and go1.27.2)

### Output of `go env` in your module/workspace:

<details>

```shell
AR='ar'
CC='gcc'
CGO_CFLAGS='-O2 -g'
CGO_CXXFLAGS='-O2 -g'
CGO_ENABLED='1'
CGO_FFLAGS='-O2 -g'
CGO_LDFLAGS='-O2 -g'
CXX='g++'
GCCGO='gccgo'
GOAMD64='v1'
GOARCH='amd64'
GOAUTH='netrc'
GOFIPS140='off'
GOHOSTARCH='amd64'
GOHOSTOS='linux'
GOOS='linux'
GOPROXY='https://proxy.golang.org,direct'
GOSUMDB='sum.golang.org'
GOTOOLCHAIN='go1.27.3'
GOVERSION='go1.27.3'
PKG_CONFIG='pkg-config'
```

(Lines with local paths and empty values removed.)

</details>

### What did you do?

Two interface types with the same methods have identical underlying types, so `*I1` converts to `*I2` without `unsafe`:

```go
package main

import "fmt"

type I1 interface{ M() }
type I2 interface{ M() }

type T struct{ x int }

func (T) M() {}

func main() {
	var a I1 = T{1}
	b := *(*I2)(&a) // *I1 converts to *I2: identical underlying types
	var c I2 = T{1}

	_, ok := b.(T)
	fmt.Println(ok)               // false
	fmt.Println(b == c)           // false
	fmt.Println(any(b) == any(c)) // true
	fmt.Printf("%T\n", b)         // main.T
	_ = b.(T)                     // panics
}
```

### What did you see happen?

```
false
false
true
main.T
panic: interface conversion: main.I2 is main.T, not main.T (types from different scopes)
```

A type switch on `b` also misses `case T`, and a `map[I2]int` holding `c` does not find `b`. The same happens with `type J I1` and `*(*J)(&a)`, and with `*(*interface{ M() })(&a)`.

`b` keeps the itab of `(T, I1)`, and `b.(T)` and `==` compare itabs rather than dynamic types. The value conversion `I2(a)` works, since it recomputes the itab (#18595); a pointer conversion cannot.

### What did you expect to see?

`true`, `true`, `true`, `main.T`, and no panic: `b`'s dynamic type is `T`, so by the spec `b.(T)` holds and `b == c`, as `any(b) == any(c)` already does. If the conversion should be rejected instead, the spec's conversion rules need to say so. The panic's "types from different scopes" is misleading too: both are `main.T`.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.
