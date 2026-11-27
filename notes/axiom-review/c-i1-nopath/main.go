// Command renamewindow drives the T10 rename window of C-I1 (dbCrash without the path) on
// configuration C: an old bbolt database at DIR/db keeps committing while a second, synced bbolt
// file DIR/snap.db is renamed onto DIR/db (etcd's OpenSnapshotBackend), the new file opened by the
// name and committing too, and, after a delay, the directory synced (the fork's syncDir). Each step
// is logged to LOG (outside the crashing device) so that a power loss's image can be checked against
// the claims the restated axiom makes (rename-window.sh).
//
//	renamewindow setup DIR
//	[RW_FORK=1] renamewindow run DIR LOG T1ms T2ms
//	renamewindow check DIR LOG
package main

import (
	"bufio"
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"time"

	bolt "go.etcd.io/bbolt"
)

var bk = []byte("b")

func must(err error) {
	if err != nil {
		panic(err)
	}
}

func mk(path string, kv map[string]string) {
	db, err := bolt.Open(path, 0600, nil)
	must(err)
	must(db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucketIfNotExists(bk)
		if err != nil {
			return err
		}
		for k, v := range kv {
			if err := b.Put([]byte(k), []byte(v)); err != nil {
				return err
			}
		}
		return nil
	}))
	must(db.Close())
}

func syncDir(dir string) {
	d, err := os.Open(dir)
	must(err)
	must(d.Sync())
	must(d.Close())
}

// commitLoop commits key `key` = 1, 2, ... with filler values of varying size (so that the file
// grows: DB.grow's truncate and sync), logging "<tag>A i" before Commit and "<tag>R i" after it
// returned.
func commitLoop(db *bolt.DB, key, tag string, logf func(string)) {
	for i := 1; ; i++ {
		tx, err := db.Begin(true)
		must(err)
		b := tx.Bucket(bk)
		must(b.Put([]byte(key), []byte(strconv.Itoa(i))))
		must(b.Put([]byte(fmt.Sprintf("%s-f%d", key, i%64)), make([]byte, (i*397)%6000)))
		logf(fmt.Sprintf("%sA %d", tag, i))
		must(tx.Commit())
		logf(fmt.Sprintf("%sR %d", tag, i))
	}
}

// forkOrder (RW_FORK=1): the fork's OpenSnapshotBackend order (e94f33b50): rename, syncDir, then open;
// only the old database commits in the window. Otherwise the new file is opened (and committed to)
// right after the rename, before the directory sync.
var forkOrder = os.Getenv("RW_FORK") == "1"

func run(dir, logPath string, t1, t2 int) {
	lf, err := os.OpenFile(logPath, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	must(err)
	var mu sync.Mutex
	logf := func(s string) {
		mu.Lock()
		defer mu.Unlock()
		_, err := lf.WriteString(s + "\n")
		must(err)
	}
	old, err := bolt.Open(filepath.Join(dir, "db"), 0600, nil)
	must(err)
	logf("OPEN")
	go commitLoop(old, "n", "", logf)
	time.Sleep(time.Duration(t1) * time.Millisecond)
	must(os.Rename(filepath.Join(dir, "snap.db"), filepath.Join(dir, "db")))
	logf("RENAMED")
	openNew := func() {
		nw, err := bolt.Open(filepath.Join(dir, "db"), 0600, nil)
		must(err)
		logf("NEWOPEN")
		go commitLoop(nw, "m", "N", logf)
	}
	if !forkOrder {
		openNew()
	}
	time.Sleep(time.Duration(t2) * time.Millisecond)
	syncDir(dir)
	logf("DIRSYNC")
	if forkOrder {
		openNew()
	}
	select {}
}

type state struct {
	lastR, lastA, nLastR, nLastA int
	renamed, newOpen, dirSync bool
}

func readLog(path string) state {
	f, err := os.Open(path)
	must(err)
	defer f.Close()
	var s state
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		fs := strings.Fields(sc.Text())
		if len(fs) == 0 {
			continue
		}
		n := 0
		if len(fs) == 2 {
			n, _ = strconv.Atoi(fs[1])
		}
		switch fs[0] {
		case "A":
			s.lastA = n
		case "R":
			s.lastR = n
		case "NA":
			s.nLastA = n
		case "NR":
			s.nLastR = n
		case "RENAMED":
			s.renamed = true
		case "NEWOPEN":
			s.newOpen = true
		case "DIRSYNC":
			s.dirSync = true
		}
	}
	return s
}

func readInt(b *bolt.Bucket, k string) (int, bool) {
	v := b.Get([]byte(k))
	if v == nil {
		return 0, false
	}
	n, err := strconv.Atoi(string(v))
	must(err)
	return n, true
}

// allowed: the restated dbCrash's set for a record (Dl, Dn, pd) as the log shows it at the crash:
// Dn the last returned commit (or the one before it, if a commit is in flight its predecessor is
// the fallback), pd the announced one.
func allowed(v, lastR, lastA int) bool {
	return v == lastR || v == lastR-1 || (lastA > lastR && v == lastA)
}

func check(dir, logPath string) {
	s := readLog(logPath)
	_, snapErr := os.Stat(filepath.Join(dir, "snap.db"))
	snapThere := snapErr == nil
	db, err := bolt.Open(filepath.Join(dir, "db"), 0400, &bolt.Options{ReadOnly: true})
	if err != nil {
		fmt.Printf("BAD open db: %v (log %+v)\n", err, s)
		return
	}
	defer db.Close()
	verdict := "ok"
	desc := ""
	must(db.View(func(tx *bolt.Tx) error {
		b := tx.Bucket(bk)
		if b == nil {
			verdict, desc = "BAD", "no bucket"
			return nil
		}
		if _, isNew := readInt(b, "snap"); isNew {
			m, _ := readInt(b, "m")
			desc = fmt.Sprintf("db=new m=%d (NR %d NA %d) snap.db there=%v", m, s.nLastR, s.nLastA, snapThere)
			if !s.renamed || snapThere {
				verdict = "BAD"
			}
			if !allowed(m, s.nLastR, s.nLastA) && !(m == 0 && s.nLastR <= 1) {
				verdict = "BAD"
			}
			return nil
		}
		n, _ := readInt(b, "n")
		desc = fmt.Sprintf("db=old n=%d (R %d A %d) snap.db there=%v", n, s.lastR, s.lastA, snapThere)
		if s.dirSync || !snapThere {
			verdict = "BAD"
		}
		if !allowed(n, s.lastR, s.lastA) && !(n == 0 && s.lastR <= 1) {
			verdict = "BAD"
		}
		return nil
	}))
	phase := "before-rename"
	if s.dirSync {
		phase = "after-dirsync"
	} else if s.newOpen {
		phase = "window(new open)"
	} else if s.renamed {
		phase = "window"
	}
	fmt.Printf("%s phase=%s %s\n", verdict, phase, desc)
}

func main() {
	switch os.Args[1] {
	case "setup":
		dir := os.Args[2]
		must(os.MkdirAll(dir, 0755))
		mk(filepath.Join(dir, "db"), map[string]string{"n": "0"})
		mk(filepath.Join(dir, "snap.db"), map[string]string{"snap": "1", "m": "0"})
		syncDir(dir)
	case "run":
		t1, _ := strconv.Atoi(os.Args[4])
		t2, _ := strconv.Atoi(os.Args[5])
		run(os.Args[2], os.Args[3], t1, t2)
	case "check":
		check(os.Args[2], os.Args[3])
	}
}
