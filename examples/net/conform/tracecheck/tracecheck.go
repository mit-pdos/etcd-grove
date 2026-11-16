// Package tracecheck loads conformance trace directories (examples/net/conform/README.md, "The
// trace format") and checks that they are well formed: every line JSON, every file a header
// and then records of its kind, every record with its operation's fields, every begin record
// with its end record unless the process ended (was killed, or exited) inside the call, every
// socket named by an operation made earlier (or one the tracer did not see made). It also
// counts what the traces hold, for the collection's summary. It does not check the traces
// against the model: that is the conformance checker's work.
package tracecheck

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path"
	"path/filepath"
	"sort"
	"strings"
)

// Version is the format version this package reads.
const Version = 1

// Rec is one record, as decoded JSON.
type Rec map[string]any

func (r Rec) str(k string) string {
	s, _ := r[k].(string)
	return s
}

func (r Rec) num(k string) (int64, bool) {
	f, ok := r[k].(float64)
	return int64(f), ok
}

func (r Rec) obj(k string) Rec {
	m, _ := r[k].(map[string]any)
	return Rec(m)
}

// Proc is one trace file: one process, a node's (role "node") or a driver's (role "driver").
type Proc struct {
	File      string
	Header    Rec
	Role      string
	Pid       int64
	Node      string
	Recs      []Rec
	Truncated bool // the last line is not JSON (a record cut short by a kill)
}

// Dir is a trace directory: the files of one run of a system.
type Dir struct {
	Name  string
	Procs []*Proc
}

// Load reads every *.jsonl file of dir.
func Load(dir string) (*Dir, error) {
	ents, err := os.ReadDir(dir)
	if err != nil {
		return nil, err
	}
	d := &Dir{Name: dir}
	for _, e := range ents {
		if e.IsDir() || !strings.HasSuffix(e.Name(), ".jsonl") {
			continue
		}
		b, err := os.ReadFile(filepath.Join(dir, e.Name()))
		if err != nil {
			return nil, err
		}
		p, err := parse(e.Name(), b)
		if err != nil {
			return nil, fmt.Errorf("%s: %v", filepath.Join(dir, e.Name()), err)
		}
		d.Procs = append(d.Procs, p)
	}
	return d, nil
}

// Dirs is every directory under root that holds trace files.
func Dirs(root string) ([]string, error) {
	seen := map[string]bool{}
	var out []string
	err := filepath.WalkDir(root, func(p string, e os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !e.IsDir() && strings.HasSuffix(p, ".jsonl") && !seen[filepath.Dir(p)] {
			seen[filepath.Dir(p)] = true
			out = append(out, filepath.Dir(p))
		}
		return nil
	})
	sort.Strings(out)
	return out, err
}

// LoadTarGz reads a gzipped tar of trace directories (testdata's samples): one Dir per
// directory in it.
func LoadTarGz(file string) ([]*Dir, error) {
	f, err := os.Open(file)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	z, err := gzip.NewReader(f)
	if err != nil {
		return nil, err
	}
	tr := tar.NewReader(z)
	dirs := map[string]*Dir{}
	var names []string
	for {
		h, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return nil, err
		}
		if h.Typeflag != tar.TypeReg || !strings.HasSuffix(h.Name, ".jsonl") {
			continue
		}
		b, err := io.ReadAll(tr)
		if err != nil {
			return nil, err
		}
		dn := path.Dir(h.Name)
		p, err := parse(path.Base(h.Name), b)
		if err != nil {
			return nil, fmt.Errorf("%s: %s: %v", file, h.Name, err)
		}
		if dirs[dn] == nil {
			dirs[dn] = &Dir{Name: dn}
			names = append(names, dn)
		}
		dirs[dn].Procs = append(dirs[dn].Procs, p)
	}
	sort.Strings(names)
	var out []*Dir
	for _, n := range names {
		out = append(out, dirs[n])
	}
	return out, nil
}

func parse(name string, b []byte) (*Proc, error) {
	p := &Proc{File: name}
	lines := bytes.Split(b, []byte("\n"))
	if len(lines) > 0 && len(lines[len(lines)-1]) == 0 {
		lines = lines[:len(lines)-1]
	} else if len(lines) > 0 {
		// No final newline: the last record was cut short.
		p.Truncated = true
		lines = lines[:len(lines)-1]
	}
	for i, l := range lines {
		var r Rec
		if err := json.Unmarshal(l, &r); err != nil {
			if i == len(lines)-1 {
				p.Truncated = true
				break
			}
			return nil, fmt.Errorf("line %d: not JSON: %v", i+1, err)
		}
		if i == 0 {
			p.Header = r
			continue
		}
		p.Recs = append(p.Recs, r)
	}
	if p.Header == nil {
		return nil, fmt.Errorf("no header")
	}
	if p.Header.str("k") != "H" {
		return nil, fmt.Errorf("line 1 is not a header record")
	}
	if v, _ := p.Header.num("v"); v != Version {
		return nil, fmt.Errorf("format version %v, want %d", p.Header["v"], Version)
	}
	p.Role = p.Header.str("role")
	p.Pid, _ = p.Header.num("pid")
	p.Node = p.Header.str("node")
	return p, nil
}

// Stats counts what a set of trace directories holds.
type Stats struct {
	Dirs, NodeProcs, DriverProcs, Records, Calls int
	Truncated                                    int            // last lines cut short
	Kills                                        int            // driver kill events
	KilledProcs                                  int            // processes ended by SIGKILL
	Unfinished                                   int            // begin records with no end, in killed processes
	UnfinishedExit                               int            // ... in processes that exited (calls in progress at the exit)
	UnfinishedUnknown                            int            // ... in processes with no exit event (lenient)
	Ops                                          map[string]int // calls by op ("Unmodeled <api>")
	Facts                                        map[string]int // noteworthy outcomes (README.md, "What the traces show")
}

func (s *Stats) fact(k string) { s.Facts[k]++ }

// NewStats is an empty Stats.
func NewStats() *Stats { return &Stats{Ops: map[string]int{}, Facts: map[string]int{}} }

// String is a summary, one count per line.
func (s *Stats) String() string {
	var b strings.Builder
	fmt.Fprintf(&b, "directories %d, node processes %d, driver processes %d, records %d, calls %d\n",
		s.Dirs, s.NodeProcs, s.DriverProcs, s.Records, s.Calls)
	fmt.Fprintf(&b, "kill events %d, processes ended by SIGKILL %d, calls cut short by a kill %d, calls in progress at an exit %d, last lines cut short %d\n",
		s.Kills, s.KilledProcs, s.Unfinished, s.UnfinishedExit, s.Truncated)
	if s.UnfinishedUnknown > 0 {
		fmt.Fprintf(&b, "calls with no end in processes with no exit event %d\n", s.UnfinishedUnknown)
	}
	for _, m := range []struct {
		name string
		m    map[string]int
	}{{"calls by op", s.Ops}, {"outcomes", s.Facts}} {
		fmt.Fprintf(&b, "%s:\n", m.name)
		keys := make([]string, 0, len(m.m))
		for k := range m.m {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for _, k := range keys {
			fmt.Fprintf(&b, "  %-72s %d\n", k, m.m[k])
		}
	}
	return b.String()
}

// Options relax the check.
type Options struct {
	// Lenient allows a begin record with no end in a process that no driver event says ended
	// (the semantics tests' child processes, which their test kills itself).
	Lenient bool
}

type call struct {
	b, e Rec
}

// Check checks d, adding its counts to st, and returns the problems found.
func Check(d *Dir, st *Stats, opt Options) []error {
	var errs []error
	bad := func(p *Proc, format string, args ...any) {
		errs = append(errs, fmt.Errorf("%s/%s: %s", d.Name, p.File, fmt.Sprintf(format, args...)))
	}
	st.Dirs++
	killed := map[int64]bool{} // pid -> ended by SIGKILL (an exit event)
	ended := map[int64]bool{}  // pid -> has an exit event
	timens := ""
	for _, p := range d.Procs {
		st.Records += len(p.Recs) + 1
		if p.Truncated {
			st.Truncated++
		}
		if tn := p.Header.str("timens"); timens == "" {
			timens = tn
		} else if tn != timens {
			bad(p, "time namespace %s, another file's is %s", tn, timens)
		}
		if p.Role != "driver" {
			continue
		}
		st.DriverProcs++
		started := map[int64]bool{}
		for i, r := range p.Recs {
			if r.str("k") != "P" {
				bad(p, "record %d: kind %q in a driver file", i+2, r.str("k"))
				continue
			}
			cpid, _ := r.num("cpid")
			switch r.str("ev") {
			case "start":
				started[cpid] = true
			case "kill":
				st.Kills++
			case "exit":
				ended[cpid] = true
				if r.str("signal") == "killed" {
					killed[cpid] = true
					st.KilledProcs++
				}
			default:
				bad(p, "record %d: event %q", i+2, r.str("ev"))
			}
		}
		for cpid := range started {
			if !ended[cpid] {
				bad(p, "process %d started, no exit event", cpid)
			}
		}
	}

	type sockKey struct {
		pid int64
		id  string
	}
	var dials, accepts []call
	firstRead := map[sockKey]Rec{}
	for _, p := range d.Procs {
		if p.Role == "driver" {
			continue
		}
		if p.Role != "node" {
			bad(p, "role %q", p.Role)
			continue
		}
		st.NodeProcs++
		begun := map[int64]Rec{}
		socks := map[string]bool{}
		for i, r := range p.Recs {
			where := fmt.Sprintf("record %d (s %v)", i+2, r["s"])
			if pid, _ := r.num("pid"); pid != p.Pid || r.str("node") != p.Node {
				bad(p, "%s: pid/node %v/%v, the header's %d/%s", where, r["pid"], r["node"], p.Pid, p.Node)
			}
			s, ok := r.num("s")
			if !ok {
				bad(p, "%s: no call number", where)
				continue
			}
			if _, ok := r.num("t"); !ok {
				bad(p, "%s: no time", where)
			}
			if _, ok := r.num("g"); !ok {
				bad(p, "%s: no goroutine", where)
			}
			op := r.str("op")
			switch r.str("k") {
			case "B":
				if _, dup := begun[s]; dup {
					bad(p, "%s: call number reused", where)
				}
				begun[s] = r
				if id := r.str("id"); id != "" && id != "nil" && !strings.HasPrefix(id, "u") && !socks[id] {
					bad(p, "%s: socket %s used before a call returned it", where, id)
				}
				if msg := checkArgs(op, r); msg != "" {
					bad(p, "%s: %s", where, msg)
				}
			case "E":
				b, ok := begun[s]
				if !ok {
					bad(p, "%s: an end with no begin", where)
					continue
				}
				delete(begun, s)
				st.Calls++
				if b.str("op") != op || b.str("id") != r.str("id") || b.str("api") != r.str("api") {
					bad(p, "%s: op/id/api %s/%s/%s, its begin's %s/%s/%s", where, op, r.str("id"), r.str("api"), b.str("op"), b.str("id"), b.str("api"))
				}
				if g0, _ := b.num("g"); g0 != mustNum(r, "g") {
					bad(p, "%s: goroutine %v, its begin's %d", where, r["g"], g0)
				}
				if t0, _ := b.num("t"); mustNum(r, "t") < t0 {
					bad(p, "%s: ends before it began", where)
				}
				if msg := checkResults(op, b, r); msg != "" {
					bad(p, "%s: %s", where, msg)
				}
				if nw := r.obj("new"); nw != nil {
					socks[nw.str("id")] = true
				}
				key := op
				if op == "Unmodeled" {
					key += " " + r.str("api")
				}
				st.Ops[key]++
				facts(st, b, r)
				c := call{b, r}
				switch {
				case op == "Dial" || op == "DialTimeout":
					dials = append(dials, c)
				case op == "Accept" && r["err"] == nil:
					accepts = append(accepts, c)
				case op == "Read":
					k := sockKey{p.Pid, r.str("id")}
					if _, ok := firstRead[k]; !ok {
						firstRead[k] = r
					}
				}
			default:
				bad(p, "%s: kind %q in a node file", where, r.str("k"))
			}
		}
		for s, b := range begun {
			switch {
			case killed[p.Pid]:
				st.Unfinished++
			case ended[p.Pid]:
				st.UnfinishedExit++
			case !ended[p.Pid] && opt.Lenient:
				st.UnfinishedUnknown++
			default:
				bad(p, "call %d (%s) began and never ended, and no driver saw the process end", s, b.str("op"))
			}
		}
		if p.Truncated && !killed[p.Pid] && !(opt.Lenient && !ended[p.Pid]) {
			bad(p, "the last line is cut short, and the process was not killed")
		}
	}

	// Accepted connections whose dialer's Dial did not return them (the abandoned dials).
	type tuple struct{ local, remote string }
	dialed := map[tuple]bool{}
	for _, c := range dials {
		if nw := c.e.obj("new"); nw != nil {
			dialed[tuple{nw.obj("local").str("s"), nw.obj("remote").str("s")}] = true
		}
	}
	for _, c := range accepts {
		nw := c.e.obj("new")
		pid, _ := c.e.num("pid")
		if dialed[tuple{nw.obj("remote").str("s"), nw.obj("local").str("s")}] {
			continue
		}
		st.fact("Accept of a connection no Dial in the directory returned")
		r, ok := firstRead[sockKey{pid, nw.str("id")}]
		switch {
		case !ok:
			st.fact("  ... never read")
		case mustNum(r, "n") > 0:
			st.fact("  ... first Read: data")
		default:
			st.fact("  ... first Read: " + errShape(r.obj("err")))
		}
	}
	return errs
}

func mustNum(r Rec, k string) int64 {
	n, _ := r.num(k)
	return n
}

func has(r Rec, keys ...string) string {
	for _, k := range keys {
		if _, ok := r[k]; !ok {
			return "no " + k
		}
	}
	return ""
}

func checkArgs(op string, b Rec) string {
	switch op {
	case "Read":
		return has(b, "id", "n")
	case "Write":
		if m := has(b, "id", "n", "data"); m != "" {
			return m
		}
		if int64(len(b.str("data"))) != 2*mustNum(b, "n") {
			return "data is not n bytes"
		}
	case "Close", "CloseWrite", "LocalAddr", "RemoteAddr", "Accept", "ListenerClose", "ListenerAddr":
		return has(b, "id")
	case "SetDeadline":
		if m := has(b, "id", "which", "set"); m != "" {
			return m
		}
		if set, _ := b["set"].(bool); set {
			return has(b, "in", "wall")
		}
	case "Dial", "Listen":
		return has(b, "net", "addr")
	case "DialTimeout":
		return has(b, "net", "addr", "timeout")
	case "Unmodeled":
		return has(b, "api")
	default:
		return "unknown op " + op
	}
	return ""
}

func checkResults(op string, b, e Rec) string {
	switch op {
	case "LocalAddr", "RemoteAddr", "ListenerAddr":
		return has(e, "addr")
	}
	if m := has(e, "err"); m != "" {
		return m
	}
	ok := e["err"] == nil
	switch op {
	case "Read":
		n := mustNum(e, "n")
		if n < 0 || n > mustNum(b, "n") {
			return "count out of range"
		}
		if (n > 0) != (e["data"] != nil) || int64(len(e.str("data"))) != 2*n {
			return "data is not the n bytes read"
		}
	case "Write":
		n := mustNum(e, "n")
		if n < 0 || n > mustNum(b, "n") {
			return "count out of range"
		}
	case "Dial", "DialTimeout", "Listen", "Accept":
		if ok != (e["new"] != nil) {
			return "a new socket iff no error"
		}
	}
	return ""
}

// errShape names an error object as the summary counts it.
func errShape(e Rec) string {
	if e == nil {
		return "nil"
	}
	if b, _ := e["eof"].(bool); b {
		return "io.EOF"
	}
	s := e.str("type")
	if b, _ := e["isClosed"].(bool); b {
		s += " ErrClosed"
	}
	if b, _ := e["isDeadline"].(bool); b {
		s += " ErrDeadlineExceeded"
	}
	if t, ok := e["timeout"].(bool); ok && t {
		s += " Timeout()"
	}
	if in := e.str("inner"); in != "" {
		s += " (" + in
		if en, ok := e.num("errno"); ok {
			s += fmt.Sprintf(" errno %d", en)
		}
		s += ")"
	}
	return s
}

// facts counts the outcomes the README's "What the traces show" lists.
func facts(st *Stats, b, e Rec) {
	op := b.str("op")
	er := e.obj("err")
	switch op {
	case "Write":
		n, want := mustNum(e, "n"), mustNum(b, "n")
		switch {
		case er == nil:
			if want == 0 {
				st.fact("Write: empty, nil")
			}
		case n > 0:
			st.fact("Write: partial (0 < k < len) with " + errShape(er))
		case want == 0:
			st.fact("Write: empty, " + errShape(er))
		default:
			st.fact("Write: k = 0 with " + errShape(er))
		}
	case "Read":
		n := mustNum(e, "n")
		switch {
		case er != nil && n > 0:
			st.fact("Read: bytes and an error at once: " + errShape(er))
		case er != nil:
			st.fact("Read: " + errShape(er))
		case mustNum(b, "n") == 0:
			st.fact("Read: empty buffer, nil")
		}
	case "Dial", "DialTimeout", "Listen", "Accept", "Close", "CloseWrite", "ListenerClose", "SetDeadline":
		if er != nil {
			st.fact(op + ": " + errShape(er))
		}
	}
}
