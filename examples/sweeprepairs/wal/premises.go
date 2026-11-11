// Package walrepairs is sweep repairs 1's Go harness for the group "wal" (W1-W5): the proposed
// premises as runtime checks, run against the counterexamples (which must violate them) and the
// examples' real uses (which must satisfy them). Tests only; not translated.
package walrepairs

import (
	"errors"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"strings"
)

// NetAddrLit is the Go mirror of the proposed Lean `netAddrLit` (W5): a canonical numeric IPv4
// literal "a.b.c.d:p", each octet a decimal 0..255 written without leading zeros, not the wildcard
// 0.0.0.0, the port a decimal 1..65535 written without leading zeros. No host name, no empty host,
// no IPv6 (so no IPv4-mapped form either).
func NetAddrLit(a string) bool {
	parts := strings.Split(a, ":")
	if len(parts) != 2 {
		return false
	}
	octs := strings.Split(parts[0], ".")
	if len(octs) != 4 {
		return false
	}
	allZero := true
	for _, o := range octs {
		n, ok := decNumeral(o)
		if !ok || n > 255 {
			return false
		}
		if n != 0 {
			allZero = false
		}
	}
	if allZero {
		return false
	}
	p, ok := decNumeral(parts[1])
	return ok && 1 <= p && p <= 65535
}

// decNumeral is the value of a decimal numeral with no leading zero ("0" itself allowed).
func decNumeral(s string) (int, bool) {
	if s == "" || (len(s) > 1 && s[0] == '0') || len(s) > 6 {
		return 0, false
	}
	n := 0
	for _, c := range []byte(s) {
		if c < '0' || c > '9' {
			return 0, false
		}
		n = n*10 + int(c-'0')
	}
	return n, true
}

// resolve is the directory a path string names now: its absolute form with every symbolic link of
// its longest existing prefix resolved (the rest appended), so that two strings naming one
// directory resolve to one string.
func resolve(p string) (string, error) {
	abs, err := filepath.Abs(p)
	if err != nil {
		return "", err
	}
	rest := ""
	cur := abs
	for {
		r, err := filepath.EvalSymlinks(cur)
		if err == nil {
			return filepath.Join(r, rest), nil
		}
		if !errors.Is(err, fs.ErrNotExist) {
			return "", err
		}
		parent := filepath.Dir(cur)
		if parent == cur {
			return abs, nil
		}
		rest = filepath.Join(filepath.Base(cur), rest)
		cur = parent
	}
}

// within says whether the resolved path p is d or inside it.
func within(p, d string) bool {
	return p == d || strings.HasPrefix(p, d+string(filepath.Separator))
}

// DataDirsDistinct is the runtime check of the proposed `dataDirsAbsent`'s part (1) (W3) at one
// moment: the strings of ds name pairwise distinct directories, none inside another (os.SameFile
// on the existing ones, and their resolved paths, which also catches nesting).
func DataDirsDistinct(ds []string) error {
	res := make([]string, len(ds))
	for i, d := range ds {
		r, err := resolve(d)
		if err != nil {
			return err
		}
		res[i] = r
	}
	for i := range ds {
		for j := i + 1; j < len(ds); j++ {
			fi, ei := os.Stat(ds[i])
			fj, ej := os.Stat(ds[j])
			if ei == nil && ej == nil && os.SameFile(fi, fj) {
				return fmt.Errorf("%q and %q name one directory (os.SameFile)", ds[i], ds[j])
			}
			if within(res[i], res[j]) || within(res[j], res[i]) {
				return fmt.Errorf("%q and %q overlap (%s, %s)", ds[i], ds[j], res[i], res[j])
			}
		}
	}
	return nil
}

// DataDirFresh is the runtime check of the proposed `dataDirsAbsent`'s part (2) (W4) for one
// data directory at program start: absent, or an empty directory (no WAL, no backend file, no
// snapshot, no symbolic link).
func DataDirFresh(dd string) error {
	fi, err := os.Lstat(dd)
	if errors.Is(err, fs.ErrNotExist) {
		return nil
	}
	if err != nil {
		return err
	}
	if !fi.IsDir() {
		return fmt.Errorf("%q is not a directory (%v)", dd, fi.Mode())
	}
	var found []string
	err = filepath.WalkDir(dd, func(p string, e fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if p != dd && !e.IsDir() {
			found = append(found, p)
		}
		return nil
	})
	if err != nil {
		return err
	}
	if len(found) > 0 {
		return fmt.Errorf("%q holds %d file(s) at start, e.g. %s", dd, len(found), strings.Join(found[:min(3, len(found))], ", "))
	}
	return nil
}

// OpenFilesWithin is the runtime check of `dataDirsAbsent`'s part (1)'s "no other string names
// one of them" at one moment: every file the process has open below root lies inside exactly one
// of the data directories ds (resolved). It returns the number of such open files.
func OpenFilesWithin(root string, ds []string) (int, error) {
	rr, err := resolve(root)
	if err != nil {
		return 0, err
	}
	res := make([]string, len(ds))
	for i, d := range ds {
		if res[i], err = resolve(d); err != nil {
			return 0, err
		}
	}
	ents, err := os.ReadDir("/proc/self/fd")
	if err != nil {
		return 0, err
	}
	n := 0
	for _, e := range ents {
		t, err := os.Readlink(filepath.Join("/proc/self/fd", e.Name()))
		if err != nil || !within(t, rr) {
			continue
		}
		n++
		k := 0
		for _, d := range res {
			if within(t, d) {
				k++
			}
		}
		if k != 1 {
			return n, fmt.Errorf("open file %s is inside %d of the data directories %v", t, k, res)
		}
	}
	return n, nil
}
