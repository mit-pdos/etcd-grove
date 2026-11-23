package server

// A stress test with direct checks (the rabia-net verification's skill, TESTING.md): N servers (3 or 5, f = 1 or 2)
// in this process on loopback, with the proxies' batch size and the phase arrays' length of the kit's configurations
// (chosen at random, or RABIA_STRESS_CONF="N,f,batch,blocks"), many concurrent closed-loop clients on all proxies (so that the servers' pending queues differ
// and slots are decided NULL or unmatched), and checks of the replication invariants on the servers' ledgers:
//   - agreement: two servers that decided a slot decided the same consensus object;
//   - at most once: no client request (client id, client sequence) is in two decided slots;
//   - every reply answers its request (its client sequence), and a get's reply is the value of the latest put
//     of that key before it in the decided sequence.
// Run: RABIA_STRESS=short go test -race -run TestStress ./roles/server/ (RABIA_STRESS=long for the long version). With RABIA_FAULTS=1,
// the servers' connections go through forwarders that delay each chunk of bytes at random (in order) and cut a
// connection now and then (both directions, losing what was in flight); a request that gets no reply is then an
// unknown outcome, and the checks hold of the rest.


import (
	"fmt"
	"math/rand"
	"net"
	"os"
	"sync"
	"testing"
	"time"

	"rabia/internal/config"
	"rabia/internal/message"
	"rabia/internal/tcp"
)

func TestStress(t *testing.T) {
	// the stress test runs alone (it sets the global configuration, which other tests' routines may still read)
	if os.Getenv("RABIA_STRESS") == "" {
		t.Skip("set RABIA_STRESS=short or RABIA_STRESS=long")
	}
	nCli, nReq := 9, 30
	if os.Getenv("RABIA_STRESS") == "long" {
		nCli, nReq = 30, 200
	}
	nS, nF, batch, blocks := stressConf(t)
	t.Logf("configuration: %d servers, f %d, batch %d, phase arrays %d", nS, nF, batch, blocks)
	base := 30000 + rand.Intn(20000)
	var proxies, peers []string
	for i := 0; i < nS; i++ {
		proxies = append(proxies, fmt.Sprintf("127.0.0.1:%d", base+i))
		peers = append(peers, fmt.Sprintf("127.0.0.1:%d", base+nS+i))
	}
	c := &config.Conf
	c.Role, c.LogLevel, c.ProjectFolder, c.Peers, c.ClosedLoop = "svr", "warn", "/tmp/rabia-net-test", peers, true
	c.NServers, c.NFaulty, c.NClients, c.NConcurrency = nS, nF, nCli, 1
	c.ProxyBatchSize, c.ProxyBatchTimeout, c.ClientBatchSize = batch, 10*time.Millisecond, 1
	c.NClientRequests = nReq
	c.CalcConstants()
	c.LenBlockArray = blocks
	c.StorageMode = 0
	c.SvrLogInterval = 50 * time.Millisecond

	faults := os.Getenv("RABIA_FAULTS") != ""
	listen := peers
	if faults {
		// the servers listen behind forwarders at the peers' addresses
		listen = nil
		for i := 0; i < nS; i++ {
			listen = append(listen, fmt.Sprintf("127.0.0.1:%d", base+2*nS+i))
		}
		for i := 0; i < nS; i++ {
			forward(t, peers[i], listen[i], 2*time.Millisecond, 3000)
		}
	}
	var svrs []*Server
	for i := 0; i < nS; i++ {
		svrs = append(svrs, ServerInit(uint32(i), proxies[i], listen[i]))
	}
	var wg sync.WaitGroup
	for _, s := range svrs {
		wg.Add(1)
		go func(s *Server) { s.Prologue(); wg.Done(); s.ServerMain() }(s)
	}
	wg.Wait()

	type rec struct {
		cmd, res string
	}
	results := make([][]rec, nCli)
	var cwg sync.WaitGroup
	for ci := 0; ci < nCli; ci++ {
		cwg.Add(1)
		go func(ci int) {
			defer cwg.Done()
			ct := tcp.ClientTcpInit(uint32(ci), proxies[ci%nS])
			ct.Connect()
			r := rand.New(rand.NewSource(int64(ci)))
			for j := 0; j < nReq; j++ {
				// any 8-byte key (the kit's premise): Gen-like keys, and keys of arbitrary bytes
				// (zero bytes, the command format's own "0", "1", "ok", invalid UTF-8), from a
				// small pool so that keys are shared
				keys := []string{"key00000", "key00001", "\x00\x00\x00\x00\x00\x00\x00\x00", "0ok1ok01", "\xff\xfe1\x00ok\x80k"}
				key := keys[r.Intn(len(keys))]
				cmd := "1" + key
				if r.Intn(2) == 0 {
					cmd = "0" + key + fmt.Sprintf("v%d-%d", ci, j)
				}
				ct.SendChan <- message.Command{CliId: uint32(ci), CliSeq: uint32(j), Commands: []string{cmd}}
				wait := 20 * time.Second
				if faults {
					wait = 2 * time.Second
				}
				timeout := time.After(wait)
			wait:
				for {
					select {
					case rep := <-ct.RecvChan:
						if rep.CliId != uint32(ci) {
							t.Errorf("client %d: a reply for client %d", ci, rep.CliId)
						}
						if rep.CliSeq != uint32(j) {
							continue
						}
						if len(rep.Commands) != 1 {
							t.Errorf("client %d: reply %v", ci, rep)
						}
						results[ci] = append(results[ci], rec{cmd, rep.Commands[0]})
						break wait
					case <-timeout:
						if !faults {
							t.Errorf("client %d: request %d timed out", ci, j)
						}
						results[ci] = append(results[ci], rec{cmd, "(unknown)"})
						break wait
					}
				}
			}
		}(ci)
	}
	cwg.Wait()
	time.Sleep(500 * time.Millisecond)

	// the decided slots of each server
	type key struct{ id, seq uint32 }
	decs := make([][]message.ConsensusObj, nS)
	for i, s := range svrs {
		for slot := 0; slot < int(c.LenLedger); slot++ {
			d, ok := s.Ledger[slot].GetDecision()
			if !ok {
				break
			}
			decs[i] = append(decs[i], d)
		}
	}
	nulls := 0
	for slot := 0; ; slot++ {
		var first *message.ConsensusObj
		any := false
		for i := 0; i < nS; i++ {
			if slot >= len(decs[i]) {
				continue
			}
			any = true
			d := decs[i][slot]
			if first == nil {
				first = &d
			} else if d.IsNull != first.IsNull || (!d.IsNull && !message.ProxySeqIdEqual(&d, first)) {
				t.Fatalf("agreement: slot %d: server %d decided %v, another %v", slot, i, d, *first)
			}
		}
		if !any {
			break
		}
		if first.IsNull {
			nulls++
		}
	}
	longest := decs[0]
	for i := 1; i < nS; i++ {
		if len(decs[i]) > len(longest) {
			longest = decs[i]
		}
	}
	seen := map[key]int{}
	state := map[string]string{}
	expect := map[key]string{}
	for slot, d := range longest {
		if d.IsNull {
			continue
		}
		for k, cid := range d.CliIds {
			id := key{cid, d.CliSeqs[k]}
			if s, ok := seen[id]; ok {
				t.Fatalf("at most once: request %v decided in slots %d and %d", id, s, slot)
			}
			seen[id] = slot
			cmd := d.Commands[k]
			kk := cmd[1 : 1+c.KeyLen]
			if cmd[0] == '0' {
				state[kk] = cmd[1+c.KeyLen:]
				expect[id] = "0" + kk + "ok"
			} else {
				expect[id] = "1" + kk + state[kk]
			}
		}
	}
	for ci := 0; ci < nCli; ci++ {
		for j, r := range results[ci] {
			if r.res == "(unknown)" {
				continue
			}
			if e, ok := expect[key{uint32(ci), uint32(j)}]; !ok || e != r.res {
				t.Fatalf("client %d request %d (%s): reply %q, the decided sequence gives %q (decided: %v)", ci, j,
					r.cmd, r.res, e, ok)
			}
		}
	}
	t.Logf("%d slots decided (%d NULL), %d requests", len(longest), nulls, len(seen))
}

// stressConf is RABIA_STRESS_CONF's configuration ("N,f,batch,blocks") or one of the kit's chosen at random.
func stressConf(t *testing.T) (int, int, int, int) {
	if e := os.Getenv("RABIA_STRESS_CONF"); e != "" {
		var n, f, b, l int
		if _, err := fmt.Sscanf(e, "%d,%d,%d,%d", &n, &f, &b, &l); err != nil {
			t.Fatalf("RABIA_STRESS_CONF %q", e)
		}
		return n, f, b, l
	}
	nf := [][2]int{{3, 1}, {5, 1}, {5, 2}}[rand.Intn(3)]
	return nf[0], nf[1], []int{1, 2, 3, 10}[rand.Intn(4)], []int{2, 3, 5, 10}[rand.Intn(4)]
}

// forward listens at addr and forwards each connection to to, delaying each chunk by up to maxDelay; with cut, it
// cuts a connection with probability 1/cut per chunk.
func forward(t *testing.T, addr, to string, maxDelay time.Duration, cut int) {
	l, err := net.Listen("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	go func() {
		for {
			a, err := l.Accept()
			if err != nil {
				return
			}
			b, err := net.Dial("tcp", to)
			if err != nil {
				a.Close()
				continue
			}
			pipe := func(dst, src net.Conn, seed int64) {
				r := rand.New(rand.NewSource(seed))
				buf := make([]byte, 1+r.Intn(64))
				for {
					n, err := src.Read(buf)
					if err != nil {
						dst.Close()
						return
					}
					time.Sleep(time.Duration(r.Int63n(int64(maxDelay))))
					if cut > 0 && r.Intn(cut) == 0 {
						a.Close()
						b.Close()
						return
					}
					if _, err := dst.Write(buf[:n]); err != nil {
						src.Close()
						return
					}
				}
			}
			go pipe(b, a, rand.Int63())
			go pipe(a, b, rand.Int63())
		}
	}()
}
