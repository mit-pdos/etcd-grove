package robust

import (
	"fmt"
	"math/rand/v2"
	"sync/atomic"
	"time"
)

// A NetNemesis makes the network's faults at random, Jepsen's way: from time to time it picks a
// fault, keeps it a while, and heals it. The faults: a partition of the machines into two
// sides (at random, or one machine alone), both ways or one way, its packets dropped or refused
// with a reset; and link faults (delay, jitter, loss, duplication, reordering) on the packets to
// some machines.
type NetNemesis struct {
	Net      *Network
	Machines []*Machine    // the machines it may partition and slow down
	Pause    time.Duration // between two faults, on average
	Hold     time.Duration // how long a fault lasts, on average
	Stats    NemesisStats
}

// NemesisStats counts the faults made.
type NemesisStats struct {
	Partitions, OneWay, Isolations, Resets, LinkFaults atomic.Uint64
}

func (s *NemesisStats) String() string {
	return fmt.Sprintf("partitions %d (one way %d, a machine isolated %d, by resets %d), link faults %d",
		s.Partitions.Load(), s.OneWay.Load(), s.Isolations.Load(), s.Resets.Load(), s.LinkFaults.Load())
}

// randDur is a random duration below 2*d.
func randDur(d time.Duration) time.Duration {
	if d <= 0 {
		return 0
	}
	return time.Duration(rand.Int64N(int64(2 * d)))
}

// sleep waits a random time below 2*d, or until stop; it says whether to stop.
func sleep(d time.Duration, stop <-chan struct{}) bool {
	select {
	case <-stop:
		return true
	case <-time.After(randDur(d)):
		return false
	}
}

// RandomPartition is a random partition of ms into two sides: one machine alone one time in
// three, otherwise each machine on a side at random (both sides non-empty if ms has two or more).
func RandomPartition(ms []*Machine) (a, b []*Machine, isolated bool) {
	if len(ms) < 2 {
		return ms, nil, false
	}
	if rand.IntN(3) == 0 {
		i := rand.IntN(len(ms))
		for j, m := range ms {
			if j != i {
				b = append(b, m)
			}
		}
		return []*Machine{ms[i]}, b, true
	}
	for len(a) == 0 || len(b) == 0 {
		a, b = nil, nil
		for _, m := range ms {
			if rand.IntN(2) == 0 {
				a = append(a, m)
			} else {
				b = append(b, m)
			}
		}
	}
	return a, b, false
}

// RandomLink is random link faults: a delay below 10ms with jitter, loss below 10%, duplication
// below 5%, reordering below 20%, each present one time in two.
func RandomLink() LinkFaults {
	var f LinkFaults
	if rand.IntN(2) == 0 {
		f.Delay = time.Duration(1+rand.IntN(10)) * time.Millisecond
		f.Jitter = time.Duration(rand.Int64N(int64(f.Delay)))
	}
	if rand.IntN(2) == 0 {
		f.Loss = rand.Float64() * 10
	}
	if rand.IntN(2) == 0 {
		f.Duplicate = rand.Float64() * 5
	}
	if rand.IntN(2) == 0 {
		f.Reorder = rand.Float64() * 20
	}
	return f
}

// Step makes one random fault, and returns the function that heals it.
func (n *NetNemesis) Step() (heal func() error, err error) {
	if rand.IntN(3) == 0 {
		// link faults on the packets to one to three machines
		var hit []*Machine
		for k := 1 + rand.IntN(3); k > 0; k-- {
			m := n.Machines[rand.IntN(len(n.Machines))]
			if err := n.Net.SetLink(m, RandomLink()); err != nil {
				return nil, err
			}
			hit = append(hit, m)
		}
		n.Stats.LinkFaults.Add(1)
		return func() error {
			for _, m := range hit {
				if err := n.Net.SetLink(m, LinkFaults{}); err != nil {
					return err
				}
			}
			return nil
		}, nil
	}
	a, b, isolated := RandomPartition(n.Machines)
	reset := n.Net.CanReset() && rand.IntN(4) == 0
	var bs []Block
	if rand.IntN(4) == 0 {
		// one way: a's packets to b are lost, b's to a arrive
		for _, x := range a {
			for _, y := range b {
				bs = append(bs, Block{From: x, To: y, Reset: reset})
			}
		}
		n.Stats.OneWay.Add(1)
	} else {
		bs = Partition([][]*Machine{a, b}, reset)
	}
	if err := n.Net.SetBlocks(bs); err != nil {
		return nil, err
	}
	n.Stats.Partitions.Add(1)
	if isolated {
		n.Stats.Isolations.Add(1)
	}
	if reset {
		n.Stats.Resets.Add(1)
	}
	return n.Net.Heal, nil
}

// Run makes faults until stop, each held a random time, then healed; the network is healed when
// it returns. It returns the first error of the commands that make or heal them.
func (n *NetNemesis) Run(stop <-chan struct{}) error {
	defer n.HealAll()
	for !sleep(n.Pause, stop) {
		heal, err := n.Step()
		if err != nil {
			return err
		}
		stopped := sleep(n.Hold, stop)
		if err := heal(); err != nil {
			return err
		}
		if stopped {
			return nil
		}
	}
	return nil
}

// HealAll removes every fault of the network.
func (n *NetNemesis) HealAll() error {
	err := n.Net.Heal()
	for _, m := range n.Machines {
		if e := n.Net.SetLink(m, LinkFaults{}); e != nil && err == nil {
			err = e
		}
	}
	return err
}
