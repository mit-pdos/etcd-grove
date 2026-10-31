// Package twoways holds programs for which both answers are behaviours of the
// model of notes/osfs-ext-plan.md, so that neither
// {{ True }} testX(dir) {{ RET true }} nor {{ RET false }} is provable.
//
// Two are racing programs (testReadAtRacingWriteAt, testStatRacingExtend):
// a racing pread or fstat returns any answer ReadSees or StatSees allows
// (plan D8), and the program asks for one of them. The others are boot
// programs.
//
// Each boot program runs when the node starts and again after every
// crash, and works out from the files which phase it is in. A setup phase ends
// in waitForCrash, which never returns, so only a crash ends it and only the
// observing phase returns. Its answer depends on what the crash kept, and the
// model allows both. Every phase's state is kept in synced bytes of a file a
// crash has already kept (plan D4), so that the phases cannot be confused.
// On an error a boot waits for the crash too.
//
// ../README.md says why each answer is possible, on Linux and in the model.
package twoways

import (
	"io"
	"os"
	"sync"
)

const pageSize = 4096

// waitForCrash ends a boot that has set up what a later boot observes.
func waitForCrash() bool {
	for {
	}
}

// Data written but not synced, read after a crash (plan D1). Byte 0 of
// dir+"/phase" is the phase, byte 0 of dir+"/data" the payload. With both
// files kept by a crash, phase 'A' and payload 'X' (synced), a boot
// overwrites the payload with 'B' without syncing it, then sets the phase to
// 'V' (synced). A boot that sees 'V' answers whether 'B' survived.
func bootUnsyncedData(dir string) bool {
	p, err := os.OpenFile(dir+"/phase", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return waitForCrash()
	}
	d, err := os.OpenFile(dir+"/data", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return waitForCrash()
	}
	var phase, data [1]byte
	np, err := p.ReadAt(phase[:], 0)
	if err != nil && err != io.EOF {
		return waitForCrash()
	}
	nd, err := d.ReadAt(data[:], 0)
	if err != nil && err != io.EOF {
		return waitForCrash()
	}
	if np == 1 && phase[0] == 'V' {
		return nd == 1 && data[0] == 'B'
	}
	if np == 1 && phase[0] == 'A' && nd == 1 && data[0] == 'X' {
		if _, err := d.WriteAt([]byte{'B'}, 0); err != nil {
			return waitForCrash()
		}
		if _, err := p.WriteAt([]byte{'V'}, 0); err != nil {
			return waitForCrash()
		}
		_ = p.Sync()
		return waitForCrash()
	}
	if _, err := d.WriteAt([]byte{'X'}, 0); err != nil {
		return waitForCrash()
	}
	if err := d.Sync(); err != nil {
		return waitForCrash()
	}
	if np == 0 || phase[0] != 'A' {
		if _, err := p.WriteAt([]byte{'A'}, 0); err != nil {
			return waitForCrash()
		}
		_ = p.Sync()
	}
	return waitForCrash()
}

// A file created and synced, its directory never synced (plan D4). Byte 0 of
// dir+"/marker" is the phase. Once the marker has survived a crash with 'M',
// a boot creates dir+"/new", writes one byte, syncs it, then sets the marker
// to 'N' (synced). A boot that sees 'N' answers whether dir+"/new" still holds
// its byte.
func bootUnsyncedName(dir string) bool {
	m, err := os.OpenFile(dir+"/marker", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return waitForCrash()
	}
	var buf [1]byte
	n, err := m.ReadAt(buf[:], 0)
	if err != nil && err != io.EOF {
		return waitForCrash()
	}
	if n == 1 && buf[0] == 'N' {
		g, err := os.OpenFile(dir+"/new", os.O_RDWR|os.O_CREATE, 0o666)
		if err != nil {
			return waitForCrash()
		}
		info, err := g.Stat()
		if err != nil {
			return waitForCrash()
		}
		return info.Size() == 1
	}
	if n == 1 && buf[0] == 'M' {
		g, err := os.OpenFile(dir+"/new", os.O_RDWR|os.O_CREATE, 0o666)
		if err != nil {
			return waitForCrash()
		}
		if _, err := g.WriteAt([]byte{1}, 0); err != nil {
			return waitForCrash()
		}
		if err := g.Sync(); err != nil {
			return waitForCrash()
		}
		if _, err := m.WriteAt([]byte{'N'}, 0); err != nil {
			return waitForCrash()
		}
		_ = m.Sync()
		return waitForCrash()
	}
	if _, err := m.WriteAt([]byte{'M'}, 0); err != nil {
		return waitForCrash()
	}
	_ = m.Sync()
	return waitForCrash()
}

// A sync that failed, then a sync that succeeded (plan D2). Byte 0 of
// dir+"/phase" is the phase, byte 0 of dir+"/data" the payload. With both
// files kept by a crash, phase 'A' and payload 'X', a boot writes 'B' to the
// payload and syncs; only if that sync fails does it sync again, and if the
// second sync succeeds it sets the phase to 'C' (synced). A boot that sees
// 'C' answers whether 'B' survived.
func bootFailedThenSync(dir string) bool {
	p, err := os.OpenFile(dir+"/phase", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return waitForCrash()
	}
	d, err := os.OpenFile(dir+"/data", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return waitForCrash()
	}
	var phase, data [1]byte
	np, err := p.ReadAt(phase[:], 0)
	if err != nil && err != io.EOF {
		return waitForCrash()
	}
	nd, err := d.ReadAt(data[:], 0)
	if err != nil && err != io.EOF {
		return waitForCrash()
	}
	if np == 1 && phase[0] == 'C' {
		return nd == 1 && data[0] == 'B'
	}
	if np == 1 && phase[0] == 'A' && nd == 1 && data[0] == 'X' {
		if _, err := d.WriteAt([]byte{'B'}, 0); err != nil {
			return waitForCrash()
		}
		if err := d.Sync(); err == nil {
			return waitForCrash()
		}
		if err := d.Sync(); err != nil {
			return waitForCrash()
		}
		if _, err := p.WriteAt([]byte{'C'}, 0); err != nil {
			return waitForCrash()
		}
		_ = p.Sync()
		return waitForCrash()
	}
	// set up (or redo, after a crash that lost a file or the payload): both
	// files synced; the next crash names them
	if _, err := d.WriteAt([]byte{'X'}, 0); err != nil {
		return waitForCrash()
	}
	if err := d.Sync(); err != nil {
		return waitForCrash()
	}
	if np == 0 || phase[0] != 'A' {
		if _, err := p.WriteAt([]byte{'A'}, 0); err != nil {
			return waitForCrash()
		}
		_ = p.Sync()
	}
	return waitForCrash()
}

// Truncate not synced. Byte 0 of dir+"/phase" is the phase; dir+"/data"
// holds one synced byte. With both files kept by a crash and phase 'A', a
// boot truncates the data file up to 4 KiB without syncing it, then sets the
// phase to 'V' (synced). A boot that sees 'V' answers whether the data file is
// 4 KiB.
func bootUnsyncedTruncate(dir string) bool {
	p, err := os.OpenFile(dir+"/phase", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return waitForCrash()
	}
	d, err := os.OpenFile(dir+"/data", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return waitForCrash()
	}
	var phase [1]byte
	np, err := p.ReadAt(phase[:], 0)
	if err != nil && err != io.EOF {
		return waitForCrash()
	}
	info, err := d.Stat()
	if err != nil {
		return waitForCrash()
	}
	if np == 1 && phase[0] == 'V' {
		return info.Size() == 4096
	}
	if np == 1 && phase[0] == 'A' && info.Size() == 1 {
		if err := d.Truncate(4096); err != nil {
			return waitForCrash()
		}
		if _, err := p.WriteAt([]byte{'V'}, 0); err != nil {
			return waitForCrash()
		}
		_ = p.Sync()
		return waitForCrash()
	}
	if err := d.Truncate(0); err != nil {
		return waitForCrash()
	}
	if _, err := d.WriteAt([]byte{'X'}, 0); err != nil {
		return waitForCrash()
	}
	if err := d.Sync(); err != nil {
		return waitForCrash()
	}
	if np == 0 || phase[0] != 'A' {
		if _, err := p.WriteAt([]byte{'A'}, 0); err != nil {
			return waitForCrash()
		}
		_ = p.Sync()
	}
	return waitForCrash()
}

// ReadAt racing an overlapping WriteAt (WriteTo's data copy against a writer
// reusing a free page): does the read see one version of the two pages, the
// old (all 1) or the new (all 9)? Without overlap it does; Linux (ext4) may
// return a mix. Model: each byte under the in-flight write is arbitrary
// (ReadSees).
func testReadAtRacingWriteAt(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return true
	}
	old := make([]byte, 2*pageSize)
	for i := range old {
		old[i] = 1
	}
	if _, err := f.WriteAt(old, 0); err != nil {
		return true
	}
	newData := make([]byte, 2*pageSize)
	for i := range newData {
		newData[i] = 9
	}
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		_, _ = f.WriteAt(newData, 0)
		wg.Done()
	}()
	buf := make([]byte, 2*pageSize)
	_, err = f.ReadAt(buf, 0)
	wg.Wait()
	if err != nil {
		return true
	}
	return buf[0] == buf[2*pageSize-1]
}

// Stat racing a WriteAt that extends the empty file by three pages: is the
// size the old or the new one? Linux: possibly one in between
// (generic_perform_write moves i_size page by page). Model: any size between
// the two (StatSees). The bound itself is a target (testStatRacingExtendBounded).
func testStatRacingExtend(dir string) bool {
	f, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		return true
	}
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		_, _ = f.WriteAt(make([]byte, 3*pageSize), 0)
		wg.Done()
	}()
	info, err := f.Stat()
	wg.Wait()
	if err != nil {
		return true
	}
	return info.Size() == 0 || info.Size() == 3*pageSize
}
