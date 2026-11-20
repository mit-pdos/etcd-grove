// Package overlay writes the `go build -overlay` file that adds conformance tracing to Go's own
// net package (examples/net/conform/README.md, "The tracer").
//
// For each traced function or method of GOROOT/src/net (the toolchain `go env GOROOT` names),
// the overlay's copy of its file renames the definition to netextOrig<Name>, and the added
// file zz_netext_trace.go (zz_netext_trace.go.src) defines <Name> as a wrapper that records
// the call and calls netextOrig<Name>. Only `func` lines change, and one call inside net
// (newTCPConn's SetKeepAliveConfig, which Go makes on its own: it calls the original, so the
// trace holds only the program's calls); every body is Go's. A second added file,
// GOROOT/src/runtime/zz_netext_goid.go, gives the tracer the goroutine's id.
//
// Make fails unless each rename and each call patch matches exactly one line, and unless the
// bodies the wrappers re-implement (Dial, DialTimeout, Dialer.Dial, Listen: each a call of
// Dialer.DialContext or ListenConfig.Listen) are exactly Go's: a Go release that moved or
// changed one would otherwise be traced wrongly. It refuses any Go but GoVersion, the target
// configuration's.
package overlay

import (
	_ "embed"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
)

// GoVersion is the Go release whose net sources the renames are written for (the semantics'
// target configuration, GooseLang/Ext/Net/Impl.lean, D13).
const GoVersion = "go1.27.3"

//go:embed zz_netext_trace.go.src
var traceSrc string

//go:embed zz_netext_goid.go.src
var goidSrc string

type rename struct{ recv, name string }

func methods(recv string, names ...string) []rename {
	var r []rename
	for _, n := range names {
		r = append(r, rename{recv, n})
	}
	return r
}

func concat(rs ...[]rename) []rename {
	var r []rename
	for _, x := range rs {
		r = append(r, x...)
	}
	return r
}

// renames: file of GOROOT/src/net -> the definitions renamed in it.
var renames = map[string][]rename{
	"net.go": methods("c *conn", "Read", "Write", "Close", "LocalAddr", "RemoteAddr", "SetDeadline",
		"SetReadDeadline", "SetWriteDeadline", "SetReadBuffer", "SetWriteBuffer", "File"),
	"dial.go": concat(methods("", "Dial", "DialTimeout", "Listen"),
		methods("d *Dialer", "Dial", "DialContext", "DialTCP"),
		methods("lc *ListenConfig", "Listen")),
	"tcpsock.go": concat(methods("c *TCPConn", "SyscallConn", "ReadFrom", "WriteTo", "CloseRead", "CloseWrite",
		"SetLinger", "SetKeepAlive", "SetKeepAlivePeriod", "SetNoDelay", "MultipathTCP"),
		methods("", "DialTCP", "ListenTCP"),
		methods("l *TCPListener", "SyscallConn", "AcceptTCP", "Accept", "Close", "SetDeadline", "File", "Addr")),
	"tcpsock_unix.go": methods("c *TCPConn", "SetKeepAliveConfig"),
}

// calls: file -> (old, new) call sites inside net of a traced method, made by Go itself.
var calls = map[string][][2]string{
	"tcpsock.go": {{"\t\tc.SetKeepAliveConfig(keepAliveCfg)\n", "\t\tc.netextOrigSetKeepAliveConfig(keepAliveCfg)\n"}},
}

// bodies: file -> definitions the wrappers re-implement, as Go has them (checked before the
// renames; zz_netext_trace.go.src's Dial, DialTimeout, Dialer.Dial and Listen).
var bodies = map[string][]string{
	"dial.go": {
		"func Dial(network, address string) (Conn, error) {\n\tvar d Dialer\n\treturn d.Dial(network, address)\n}\n",
		"func DialTimeout(network, address string, timeout time.Duration) (Conn, error) {\n\td := Dialer{Timeout: timeout}\n\treturn d.Dial(network, address)\n}\n",
		"func (d *Dialer) Dial(network, address string) (Conn, error) {\n\treturn d.DialContext(context.Background(), network, address)\n}\n",
		"func Listen(network, address string) (Listener, error) {\n\tvar lc ListenConfig\n\treturn lc.Listen(context.Background(), network, address)\n}\n",
	},
}

// Renamed lists the traced Go definitions ("net.go: (c *conn) Read", ...), for the README and
// the tests.
func Renamed() []string {
	var r []string
	for _, f := range []string{"net.go", "dial.go", "tcpsock.go", "tcpsock_unix.go"} {
		for _, x := range renames[f] {
			if x.recv != "" {
				r = append(r, fmt.Sprintf("%s: (%s) %s", f, x.recv, x.name))
			} else {
				r = append(r, fmt.Sprintf("%s: %s", f, x.name))
			}
		}
	}
	return r
}

func goEnv() (goroot string, err error) {
	out, err := exec.Command("go", "env", "GOROOT", "GOVERSION", "GOMODCACHE").Output()
	if err != nil {
		return "", fmt.Errorf("overlay: go env: %v", err)
	}
	f := strings.Split(strings.TrimRight(string(out), "\n"), "\n")
	if len(f) != 3 {
		return "", fmt.Errorf("overlay: go env printed %q", out)
	}
	root, ver, modcache := f[0], f[1], f[2]
	if ver != GoVersion {
		return "", fmt.Errorf("overlay: the go command is %s; the tracer is written for %s's net sources", ver, GoVersion)
	}
	rr, _ := filepath.EvalSymlinks(root)
	rm, _ := filepath.EvalSymlinks(modcache)
	if rm != "" && strings.HasPrefix(rr+string(filepath.Separator), rm+string(filepath.Separator)) {
		return "", fmt.Errorf("overlay: GOROOT %s is beneath GOMODCACHE %s: Go refuses to overlay files there; set GOMODCACHE elsewhere", root, modcache)
	}
	return root, nil
}

// Patch returns src (GOROOT/src/net/fname) with the renames and call patches of fname
// applied, or an error naming the first one that does not match exactly once.
func Patch(fname, src string) (string, error) {
	for _, b := range bodies[fname] {
		if k := strings.Count(src, b); k != 1 {
			return "", fmt.Errorf("overlay: %s: the body the tracer re-implements occurs %d times:\n%s", fname, k, b)
		}
	}
	for _, x := range renames[fname] {
		recv, newHead := "", "func netextOrig"+x.name+"("
		if x.recv != "" {
			recv = `\(` + regexp.QuoteMeta(x.recv) + `\) `
			newHead = "func (" + x.recv + ") netextOrig" + x.name + "("
		}
		pat := regexp.MustCompile(`(?m)^func ` + recv + x.name + `\(`)
		if k := len(pat.FindAllStringIndex(src, -1)); k != 1 {
			return "", fmt.Errorf("overlay: %s: %q matched %d lines", fname, pat.String(), k)
		}
		src = pat.ReplaceAllLiteralString(src, newHead)
	}
	for _, c := range calls[fname] {
		if k := strings.Count(src, c[0]); k != 1 {
			return "", fmt.Errorf("overlay: %s: the call %q occurs %d times", fname, strings.TrimSpace(c[0]), k)
		}
		src = strings.Replace(src, c[0], c[1], 1)
	}
	return src, nil
}

// Make writes the overlay's files under dir (dir/net/..., dir/runtime/...) and the overlay
// file dir/overlay.json, and returns the latter's path: `go build -overlay <path>`.
func Make(dir string) (string, error) {
	root, err := goEnv()
	if err != nil {
		return "", err
	}
	dir, err = filepath.Abs(dir)
	if err != nil {
		return "", err
	}
	replace := map[string]string{}
	write := func(pkg, name, content string) error {
		d := filepath.Join(dir, pkg)
		if err := os.MkdirAll(d, 0o755); err != nil {
			return err
		}
		dst := filepath.Join(d, name)
		if err := os.WriteFile(dst, []byte(content), 0o644); err != nil {
			return err
		}
		replace[filepath.Join(root, "src", pkg, name)] = dst
		return nil
	}
	for fname := range renames {
		b, err := os.ReadFile(filepath.Join(root, "src", "net", fname))
		if err != nil {
			return "", err
		}
		src, err := Patch(fname, string(b))
		if err != nil {
			return "", err
		}
		if err := write("net", fname, src); err != nil {
			return "", err
		}
	}
	if err := write("net", "zz_netext_trace.go", traceSrc); err != nil {
		return "", err
	}
	if err := write("runtime", "zz_netext_goid.go", goidSrc); err != nil {
		return "", err
	}
	j, err := json.MarshalIndent(map[string]any{"Replace": replace}, "", " ")
	if err != nil {
		return "", err
	}
	path := filepath.Join(dir, "overlay.json")
	if err := os.WriteFile(path, append(j, '\n'), 0o644); err != nil {
		return "", err
	}
	return path, nil
}
