// coordinator package manages the state of the chain. The Coordinator is
// responsible for detecting and handling node failures, electing head and tail
// nodes, and adding new nodes to the chain.
//
// If the Coordinator process fails but the chain is still intact, reads would
// still be possible. Writes will not be possible because all writes are first
// sent to the Coordinator. The coordinator forwards write requests to the head
// node.

package coordinator

import (
	"errors"
	"log"
	"sync"
	"time"

	"github.com/despreston/go-craq/transport"
)

const (
	pingTimeout  = 5 * time.Second
	pingInterval = 1 * time.Second
)

var ErrEmptyChain = errors.New("no nodes in the chain")

// Coordinator is responsible for tracking the Nodes in the chain.
type Coordinator struct {
	tport      transport.NodeClientFactory
	head, tail *node
	mu         sync.Mutex
	replicas   []*node

	// version is the last version assigned to a write (versions start at 1;
	// 0 means no version).
	version uint64

	// For testing the AddNode method. This WaitGroup is done when updates have
	// been sent to all nodes.
	Updates *sync.WaitGroup
}

func New(t transport.NodeClientFactory) *Coordinator {
	return &Coordinator{
		Updates: &sync.WaitGroup{},
		tport:   t,
	}
}

func (cdr *Coordinator) Start() {
	cdr.pingReplicas()
}

// Ping each node. If the response returns an error or the pingTimeout is
// reached, remove the node from the list of replicas.
func (cdr *Coordinator) pingReplicas() {
	log.Println("starting pinging")
	for {
		cdr.mu.Lock()
		replicas := append([]*node{}, cdr.replicas...)
		cdr.mu.Unlock()
		for _, n := range replicas {
			go func(n *node) {
				resultCh := make(chan bool, 1)

				go func() {
					err := n.rpc.Ping()
					resultCh <- err == nil
				}()

				select {
				case ok := <-resultCh:
					if !ok {
						cdr.RemoveNode(n.Address())
					}
				case <-time.After(pingTimeout):
					cdr.RemoveNode(n.Address())
				}
			}(n)
		}
		time.Sleep(pingInterval)
	}
}

func findReplicaIndex(address string, replicas []*node) (int, bool) {
	for i, replica := range replicas {
		if replica.Address() == address {
			return i, true
		}
	}
	return 0, false
}

// updateAll sends every node but skip its metadata (cdr.mu held).
func (cdr *Coordinator) updateAll(skip int) {
	wg := sync.WaitGroup{}
	for i := 0; i < len(cdr.replicas); i++ {
		if i == skip {
			continue
		}
		wg.Add(1)
		go func(i int) {
			cdr.updateNode(i)
			wg.Done()
		}(i)
	}
	wg.Wait()
}

var (
	errLastNode     = errors.New("cannot remove the last node of the chain")
	errDisconnected = errors.New("no metadata can be sent to the node")
)

// RemoveNode removes the node from the chain. A tail is removed only once it
// knows it is not the tail any more (it is alive, or the coordinator could not
// have told it): two nodes acting as the tail commit different versions. The
// chain's last node is never removed: it holds the committed versions.
func (cdr *Coordinator) RemoveNode(address string) error {
	cdr.mu.Lock()
	defer cdr.mu.Unlock()

	idx, found := findReplicaIndex(address, cdr.replicas)
	if !found {
		return errors.New("unknown node")
	}
	if len(cdr.replicas) == 1 {
		return errLastNode
	}

	wasTail := idx == len(cdr.replicas)-1
	if wasTail {
		// The tail stops acting as the tail before another node takes the role.
		if err := cdr.sendMeta(cdr.replicas[idx], &transport.NodeMeta{}); err != nil {
			log.Printf("Failed to tell the tail %s it is removed: %v\n", address, err)
			return err
		}
	}

	cdr.replicas = append(cdr.replicas[:idx], cdr.replicas[idx+1:]...)
	log.Printf("removed node %s", address)

	if wasTail {
		cdr.tail = cdr.replicas[idx-1]

		// The new tail first (it catches up with the removed tail), then all
		// the other nodes need to be updated to know where the tail is.
		if err := cdr.updateNode(idx - 1); err != nil {
			log.Printf("Failed to update the new tail: %v\n", err)
		}
		cdr.updateAll(idx - 1)
		return nil
	}

	// After removing the node, the successor, if there was one, now sits at idx
	// in the chain. Send a message to that node to update it's metadata.
	if len(cdr.replicas) > idx {
		err := cdr.updateNode(idx)
		if err != nil {
			log.Printf("Failed to update successor: %s\n", err.Error())
			return err
		}
	}

	// Send update to predecessor and update the tail
	if idx > 0 {
		err := cdr.updateNode(idx - 1)
		if err != nil {
			log.Printf("Failed to update predecessor: %v\n", err)
			return err
		}
	}

	return nil
}

// sendMeta sends the node its metadata (cdr.mu held). The metadata of a node is
// applied in the order it is sent: after a failed Update, which the node may
// still apply later, the node gets no more metadata.
func (cdr *Coordinator) sendMeta(n *node, meta *transport.NodeMeta) error {
	if !n.connected {
		return errDisconnected
	}
	if err := n.rpc.Update(meta); err != nil {
		n.connected = false
		return err
	}
	return nil
}

// updateNode sends the latest metadata to a Node to tell it whether it's head
// or tail and what it's neighbors' addresses are (cdr.mu held).
func (cdr *Coordinator) updateNode(i int) error {
	n := cdr.replicas[i]

	log.Printf("Sending metadata to %s.\n", n.Address())

	var args transport.NodeMeta
	args.IsHead = i == 0
	args.IsTail = len(cdr.replicas) == i+1
	args.Tail = cdr.replicas[len(cdr.replicas)-1].Address()

	if len(cdr.replicas) > 1 {
		if i > 0 {
			// Not the first node, so add address to previous.
			args.Prev = cdr.replicas[i-1].Address()
		}
		if i+1 != len(cdr.replicas) {
			// Not the last node, so add address to next.
			args.Next = cdr.replicas[i+1].Address()
		}
	}

	// call Update method on node
	return cdr.sendMeta(n, &args)
}

// AddNode should be called by Nodes to announce themselves to the Coordinator.
// The coordinator then adds them to the end of the chain: the current tail
// stops acting as the tail first, then the new node gets its metadata (it
// connects to the previous Node in the chain and catches up with it before it
// acts as the tail), then the other nodes learn the new tail, all before
// AddNode replies with the new node's metadata.
func (cdr *Coordinator) AddNode(address string) (*transport.NodeMeta, error) {
	meta, err := cdr.addNode(address)
	if err != nil {
		return nil, errors.New("failed to add node: " + err.Error())
	}
	return meta, nil
}

func (cdr *Coordinator) addNode(address string) (*transport.NodeMeta, error) {
	log.Printf("received AddNode from %s\n", address)

	n := &node{
		last:    time.Now(),
		address: address,
		rpc:     cdr.tport(),
	}

	if err := n.Connect(); err != nil {
		log.Printf("failed to connect to node %s\n", address)
		return nil, err
	}

	cdr.mu.Lock()
	defer cdr.mu.Unlock()

	if len(cdr.replicas) > 0 {
		// The tail stops acting as the tail: its successor is the new node.
		last := len(cdr.replicas) - 1
		var meta transport.NodeMeta
		meta.IsHead = last == 0
		meta.Next = address
		meta.Tail = address
		if last > 0 {
			meta.Prev = cdr.replicas[last-1].Address()
		}
		if err := cdr.sendMeta(cdr.replicas[last], &meta); err != nil {
			log.Printf("failed to update the tail for node %s: %v\n", address, err)
			return nil, err
		}
	}

	cdr.replicas = append(cdr.replicas, n)
	cdr.tail = n
	meta := &transport.NodeMeta{}
	meta.IsTail = true
	meta.Tail = address

	if len(cdr.replicas) == 1 {
		cdr.head = n
		meta.IsHead = true
	} else {
		meta.Prev = cdr.replicas[len(cdr.replicas)-2].Address()
	}

	if err := cdr.updateNode(len(cdr.replicas) - 1); err != nil {
		log.Printf("failed to set up node %s: %v\n", address, err)
		return nil, err
	}

	// Because the tail node changed, all the other nodes need to be updated to
	// know where the tail is.
	cdr.updateAll(len(cdr.replicas) - 1)

	return meta, nil
}

// ErrVersions is returned once every version number has been used.
var ErrVersions = errors.New("no version left")

// Write a new object to the chain. The coordinator, which every write goes
// through, assigns its version: one version names one write, whichever node
// is the head (a new head does not know the versions the old one assigned).
func (cdr *Coordinator) Write(key string, value []byte) error {
	cdr.mu.Lock()
	if len(cdr.replicas) < 1 {
		cdr.mu.Unlock()
		return ErrEmptyChain
	}
	if cdr.version == ^uint64(0) {
		cdr.mu.Unlock()
		return ErrVersions
	}
	cdr.version++
	version := cdr.version

	// Forward the write to the head
	head := cdr.replicas[0]
	cdr.mu.Unlock()
	if err := head.rpc.Write(key, value, version); err != nil {
		return errors.New("failed to send to the head: " + err.Error())
	}
	return nil
}
