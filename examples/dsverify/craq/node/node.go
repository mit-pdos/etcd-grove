// node package corresponds to what the CRAQ white paper refers to as a node.

package node

import (
	"errors"
	"log"
	"sync"

	"github.com/despreston/go-craq/store"
	"github.com/despreston/go-craq/transport"
)

// neighbor is another node in the chain
type neighbor struct {
	rpc     transport.NodeClient
	address string
}

// Opts is for passing options to the Node constructor.
type Opts struct {
	// Storage layer to use
	Store store.Storer
	// Local listening address
	Address string
	// Address to advertise to other nodes and coordinator
	PubAddress string
	// Address of coordinator
	CdrAddress string
	// Transport creates new clients for communication with other nodes
	Transport transport.NodeClientFactory
	// For communication with the Coordinator
	CoordinatorClient transport.CoordinatorClient
	// Log
	Log *log.Logger
}

var (
	errNoSuccessor = errors.New("no successor")
	errNoTail      = errors.New("no connection to the tail")
	errNotTail     = errors.New("not the tail")
	errTailVersion = errors.New("failed to get the latest version from the tail")
)

type commitEvent struct {
	Key     string
	Version uint64
}

// Node is what the white paper refers to as a node. This is the client that is
// responsible for storing data and handling reads/writes.
type Node struct {
	// Other nodes in the chain
	neighbors map[transport.NeighborPos]neighbor
	// Storage layer
	store store.Storer
	// Latest version of a given key
	latest map[string]uint64
	// For listening to commit's. For testing.
	committed                    chan commitEvent
	cdrAddress, address, pubAddr string
	cdr                          transport.CoordinatorClient
	IsHead, IsTail               bool
	mu                           sync.Mutex
	transport                    func() transport.NodeClient
	log                          *log.Logger
}

// New creates a new Node.
func New(opts Opts) *Node {
	logger := opts.Log
	if opts.Log == nil {
		logger = log.Default()
	}
	return &Node{
		latest:     make(map[string]uint64),
		neighbors:  make(map[transport.NeighborPos]neighbor, 3),
		cdrAddress: opts.CdrAddress,
		address:    opts.Address,
		store:      opts.Store,
		transport:  opts.Transport,
		pubAddr:    opts.PubAddress,
		cdr:        opts.CoordinatorClient,
		log:        logger,
	}
}

// ListenAndServe starts listening for messages and connects to the coordinator.
func (n *Node) Start() error {
	if err := n.backfillLatest(); err != nil {
		log.Fatalf("Failed to backfill latest versions.\n Error: %#v", err)
	}
	if err := n.connectToCoordinator(); err != nil {
		n.log.Printf("Failed to connect to the chain.\n Error: %#v", err)
		return err
	}
	return nil
}

// backfillLatest queries the store for the latest committed version of
// everything it has in order to fill n.latest.
func (n *Node) backfillLatest() error {
	c, err := n.store.AllCommitted()
	if err != nil {
		return err
	}
	n.mu.Lock()
	defer n.mu.Unlock()
	for _, item := range c {
		if n.latest[item.Key] < item.Version {
			n.latest[item.Key] = item.Version
		}
	}
	return nil
}

// ConnectToCoordinator let's the Node announce itself to the chain coordinator
// to be added to the chain. Before it replies, the coordinator sends the Node
// its place in the chain (Update): whether it's the head or tail, and the
// address of the previous node in the chain and of the tail node. The Node
// connects to the predecessor and catches up in Update, under its lock; the
// reply repeats that metadata, which Update already applied (applying it again
// here could undo a later Update).
func (n *Node) connectToCoordinator() error {
	err := n.cdr.Connect(n.cdrAddress)
	if err != nil {
		n.log.Println("Error connecting to the coordinator")
		return err
	}

	n.log.Printf("Connected to coordinator at %s\n", n.cdrAddress)

	// Announce self to the Coordinator
	if _, err := n.cdr.AddNode(n.pubAddr); err != nil {
		n.log.Println(err.Error())
		return err
	}

	return nil
}

func (n *Node) connectToNode(address string, pos transport.NeighborPos) error {
	newNbr := n.transport()
	if err := newNbr.Connect(address); err != nil {
		return err
	}

	n.log.Printf("connected to %s\n", address)

	// Disconnect from current neighbor if there's one connected.
	nbr := n.neighbors[pos]
	if nbr.rpc != nil {
		nbr.rpc.Close()
	}

	n.neighbors[pos] = neighbor{
		rpc:     newNbr,
		address: address,
	}

	return nil
}

func (n *Node) writePropagated(reply *transport.PropagateResponse) error {
	// Save items from reply to store.
	for key, forKey := range *reply {
		for _, item := range forKey {
			if err := n.store.Write(key, item.Value, item.Version); err != nil {
				n.log.Printf("Failed to write item %+v to store: %#v\n", item, err)
				return err
			}
			n.log.Printf("wrote %s", key)
		}
	}
	return nil
}

// Commit the version to the store, update n.latest for this key, and announce
// the commit to the n.committed channel if there is one. The caller holds n.mu.
// Commits arrive in any order: n.latest keeps the newest committed version.
func (n *Node) commit(key string, version uint64) error {
	if err := n.store.Commit(key, version); err != nil {
		n.log.Printf("Failed to commit. Key: %s Version: %d Error: %#v", key, version, err)
		return err
	}

	if n.latest[key] < version {
		n.latest[key] = version
	}

	if n.committed != nil {
		n.committed <- commitEvent{Key: key, Version: version}
	}

	return nil
}

func (n *Node) commitPropagated(reply *transport.PropagateResponse) error {
	// Commit items from reply to store.
	for key, forKey := range *reply {
		for _, item := range forKey {
			// It's possible the item doesn't exist. In that case, add it first.
			// This sort of a poor man's upsert, but it saves from having to
			// deal w/ it in the storage layer, which should make it easier to
			// write new storers.
			if err := n.commit(key, item.Version); err != nil {
				if err == store.ErrNotFound {
					if err := n.store.Write(key, item.Value, item.Version); err != nil {
						return err
					}
					if err := n.commit(key, item.Version); err != nil {
						return err
					}
				} else {
					return err
				}
			}
		}
	}
	return nil
}

// Create a map of the highest versions for each key.
func propagateRequestFromItems(items []*store.Item) *transport.PropagateRequest {
	req := transport.PropagateRequest{}
	for _, item := range items {
		if req[item.Key] < item.Version {
			req[item.Key] = item.Version
		}
	}
	return &req
}

// requestFwdPropagation asks client to respond with all uncommitted (dirty)
// items that this node either does not have or are newer than what this node
// has.
func (n *Node) requestFwdPropagation(client transport.NodeClient) error {
	dirty, err := n.store.AllDirty()
	if err != nil {
		n.log.Printf("Failed to get all dirty items: %#v\n", err)
		return err
	}

	reply, err := client.FwdPropagate(propagateRequestFromItems(dirty))
	if err != nil {
		n.log.Printf("Failed during forward propagation: %#v\n", err)
		return err
	}

	return n.writePropagated(reply)
}

// requestBackPropagation asks client to respond with all committed items that
// this node either does not have or are newer than what this node has.
func (n *Node) requestBackPropagation(client transport.NodeClient) error {
	committed, err := n.store.AllCommitted()
	if err != nil {
		n.log.Printf("Failed to get all committed items: %#v\n", err)
		return err
	}

	reply, err := client.BackPropagate(propagateRequestFromItems(committed))
	if err != nil {
		n.log.Printf("Failed during back propagation: %#v\n", err)
		return err
	}

	return n.commitPropagated(reply)
}

// resetNeighbor closes any open connection and resets the neighbor.
func (n *Node) resetNeighbor(pos transport.NeighborPos) {
	if nbr := n.neighbors[pos]; nbr.rpc != nil {
		nbr.rpc.Close()
	}
	n.neighbors[pos] = neighbor{}
}

// Ping responds to ping messages.
func (n *Node) Ping() error {
	return nil
}

func (n *Node) connectToPredecessor(address string) error {
	prev := n.neighbors[transport.NeighborPosPrev]

	if prev.address == address {
		n.log.Println("New predecessor same address as last one, keeping conn.")
		return nil
	} else if address == "" {
		n.log.Println("Resetting predecessor")
		n.resetNeighbor(transport.NeighborPosPrev)
		return nil
	}

	n.log.Printf("connecting to new predecessor %s\n", address)
	if err := n.connectToNode(address, transport.NeighborPosPrev); err != nil {
		return err
	}

	prevC := n.neighbors[transport.NeighborPosPrev].rpc
	return n.requestFwdPropagation(prevC)
}

func (n *Node) connectToSuccessor(address string) error {
	next := n.neighbors[transport.NeighborPosNext]

	if next.address == address {
		n.log.Println("New successor same address as last one, keeping conn.")
		return nil
	} else if address == "" {
		n.log.Println("Resetting successor")
		n.resetNeighbor(transport.NeighborPosNext)
		return nil
	}

	n.log.Printf("connecting to new successor %s\n", address)
	if err := n.connectToNode(address, transport.NeighborPosNext); err != nil {
		return err
	}

	nextC := n.neighbors[transport.NeighborPosNext].rpc
	return n.requestBackPropagation(nextC)
}

// Update is for updating a node's metadata. If new neighbors are given, the
// Node will disconnect from the current neighbors before connecting to the new
// ones. Coordinator uses this method to update metadata of the node when there
// is a failure or re-organization of the chain.
//
// The tail role moves only through the coordinator: a node told it is not the
// tail stops acting as the tail (committing, answering LatestVersion) at once,
// before the coordinator gives the role to another node; a node told it is the
// tail acts as the tail only after catching up with the committed versions of
// the previous tail, which is its successor (when the coordinator removed it)
// or its new predecessor (when this node joined after it).
func (n *Node) Update(meta *transport.NodeMeta) error {
	if err := n.update(meta); err != nil {
		return errors.New("update failed: " + err.Error())
	}
	return nil
}

func (n *Node) update(meta *transport.NodeMeta) error {
	n.log.Printf("Received metadata update: %+v\n", meta)
	n.mu.Lock()
	defer n.mu.Unlock()
	becomesTail := meta.IsTail && !n.IsTail
	if !meta.IsTail {
		n.IsTail = false
	}
	n.IsHead = meta.IsHead

	if err := n.connectToPredecessor(meta.Prev); err != nil {
		return err
	}

	// connect to tail if address is different
	tail := n.neighbors[transport.NeighborPosTail]
	if !meta.IsTail && tail.address != meta.Tail && meta.Tail != "" {
		err := n.connectToNode(meta.Tail, transport.NeighborPosTail)
		if err != nil {
			return err
		}
	}

	if becomesTail {
		// Catch up with the previous tail's committed versions, then commit
		// all dirty versions and forward the commits to the predecessor.
		prevTail := n.neighbors[transport.NeighborPosNext].rpc
		if prevTail == nil {
			prevTail = n.neighbors[transport.NeighborPosPrev].rpc
		}
		if prevTail != nil {
			if err := n.requestBackPropagation(prevTail); err != nil {
				return err
			}
		}
		n.IsTail = true

		dirty, err := n.store.AllDirty()
		if err != nil {
			n.log.Println("Error fetching all dirty items during node Update")
			return err
		}

		prev := n.neighbors[transport.NeighborPosPrev]
		for i := range dirty {
			item := dirty[i]
			if err := n.commit(item.Key, item.Version); err != nil {
				n.log.Printf(
					"Error during commit for item: %#v, error: %#v\n",
					item,
					err,
				)
				continue
			}
			go n.sendCommitToPrev(prev, item.Key, item.Version)
		}
	}

	if err := n.connectToSuccessor(meta.Next); err != nil {
		return err
	}

	return nil
}

// ClientWrite adds a new object to the chain and starts the process of
// replication.
func (n *Node) ClientWrite(key string, val []byte) error {
	// Increment version based off any existing objects for this key.
	var version uint64
	old, err := n.store.Read(key)
	if err == nil {
		version = old.Version + 1
	}

	if err := n.store.Write(key, val, version); err != nil {
		n.log.Printf("Failed to create during ClientWrite. %v\n", err)
		return err
	}

	n.log.Printf("Node RPC ClientWrite() created version %d of key %s\n", version, key)

	// Forward the new object to the successor node.

	n.mu.Lock()
	next := n.neighbors[transport.NeighborPosNext]

	// If there's no successor, it means this is the only node in the chain, so
	// mark the item as committed and return early.
	if next.address == "" {
		n.log.Println("No successor")
		err := n.commit(key, version)
		n.mu.Unlock()
		if err != nil {
			return err
		}
		return nil
	}
	n.mu.Unlock()

	if next.rpc == nil {
		return errNoSuccessor
	}
	if err := next.rpc.Write(key, val, version); err != nil {
		n.log.Printf("Failed to send to successor during ClientWrite. %v\n", err)
		return err
	}

	return nil
}

// Write adds an object to the chain. If the node is not the tail, the Write is
// forwarded to the next node in the chain. If the node is tail, the object is
// marked committed and a Commit message is sent to the predecessor in the
// chain.
func (n *Node) Write(key string, val []byte, version uint64) error {
	n.log.Printf("Node RPC Write() %s version %d to store\n", key, version)

	n.mu.Lock()
	if err := n.store.Write(key, val, version); err != nil {
		n.mu.Unlock()
		n.log.Printf("Failed to write. %v\n", err)
		return err
	}

	// If this isn't the tail node, the write needs to be forwarded along the
	// chain to the next node (without holding the lock: the commit comes back
	// through this node).
	if !n.IsTail {
		next := n.neighbors[transport.NeighborPosNext]
		n.mu.Unlock()
		if next.rpc == nil {
			return errNoSuccessor
		}
		if err := next.rpc.Write(key, val, version); err != nil {
			n.log.Printf("Failed to send to successor during Write. %v\n", err)
			return errors.New("failed to send to successor: " + err.Error())
		}
		return nil
	}

	// At this point it's assumed this node is the tail.

	err := n.commit(key, version)
	prev := n.neighbors[transport.NeighborPosPrev]
	n.mu.Unlock()
	if err != nil {
		n.log.Printf("Failed to mark as committed in Write. %v\n", err)
		return err
	}

	// Start telling predecessors to mark this version committed.
	n.sendCommitToPrev(prev, key, version)
	return nil
}

// commitAndSend commits an item to the store and sends a message to the
// predecessor node to tell it to commit as well.
func (n *Node) commitAndSend(key string, version uint64) error {
	n.mu.Lock()
	err := n.commit(key, version)
	prev := n.neighbors[transport.NeighborPosPrev]
	n.mu.Unlock()
	if err != nil {
		return err
	}

	// if this node has a predecessor, send commit to previous node
	if prev.address != "" {
		return n.sendCommitToPrev(prev, key, version)
	}

	return nil
}

// sendCommitToPrev sends the commit to prev, the predecessor read under n.mu.
func (n *Node) sendCommitToPrev(prev neighbor, key string, version uint64) error {
	if prev.rpc == nil {
		return nil
	}
	if err := prev.rpc.Commit(key, version); err != nil {
		n.log.Printf("Failed to send Commit to predecessor. %v\n", err)
		return errors.New("failed to send commit to predecessor: " + err.Error())
	}
	return nil
}

// Commit marks an object as committed in storage.
func (n *Node) Commit(key string, version uint64) error {
	return n.commitAndSend(key, version)
}

// Read returns the value of the key's latest committed version. The tail
// knows it: a node that is the tail reads it from its store; any other node asks
// the tail for the latest committed version and reads that version from its own
// store. (A node cannot tell from its own store whether its newest clean
// version is still the latest committed one: the coordinator may have removed
// it from the chain, or not caught it up yet.) Errors other than "key doesn't
// exist" mean that the read could not tell.
func (n *Node) Read(key string) (string, []byte, error) {
	n.mu.Lock()
	if n.IsTail {
		v := n.latest[key]
		if v == 0 {
			n.mu.Unlock()
			return "", nil, errors.New("key doesn't exist")
		}
		item, err := n.store.ReadVersion(key, v)
		n.mu.Unlock()
		if err != nil {
			return "", nil, err
		}
		return key, item.Value, nil
	}
	tail := n.neighbors[transport.NeighborPosTail]
	n.mu.Unlock()
	if tail.rpc == nil {
		return "", nil, errNoTail
	}

	_, v, err := tail.rpc.LatestVersion(key)
	if err != nil {
		n.log.Printf(
			"Failed to get latest version of %s from the tail. %v\n",
			key,
			err,
		)
		return "", nil, errTailVersion
	}
	if v == 0 {
		return "", nil, errors.New("key doesn't exist")
	}

	item, err := n.store.ReadVersion(key, v)
	if err != nil {
		return "", nil, err
	}

	return key, item.Value, nil
}

// ReadAll returns all committed key/value pairs in the store.
func (n *Node) ReadAll() (*[]transport.Item, error) {
	fullItems, err := n.store.AllCommitted()
	if err != nil {
		return nil, err
	}

	items := []transport.Item{}
	for _, itm := range fullItems {
		items = append(items, transport.Item{
			Key:   itm.Key,
			Value: itm.Value,
		})
	}

	return &items, nil
}

// LatestVersion provides the latest committed version for a given key in the
// store.
//
// Only the tail answers: another node's latest committed version may be older.
func (n *Node) LatestVersion(key string) (string, uint64, error) {
	n.mu.Lock()
	defer n.mu.Unlock()
	if !n.IsTail {
		return "", 0, errNotTail
	}
	return key, n.latest[key], nil
}

// BackPropagate let's another node ask this node to send it all the committed
// items it has in it's storage. The node requesting back propagation should
// send the key + latest version of all committed items it has. This node
// responds with all committed items that: have a newer version, weren't
// included in the request.
func (n *Node) BackPropagate(
	verByKey *transport.PropagateRequest,
) (*transport.PropagateResponse, error) {
	unseen, err := n.store.AllNewerCommitted(map[string]uint64(*verByKey))
	if err != nil {
		return nil, err
	}
	return makePropagateResponse(unseen), nil
}

// FwdPropagate let's another node ask this node to send it all the dirty items
// it has in it's storage. The node requesting forward propagation should send
// the key + latest version of all uncommitted items it has. This node responds
// with all uncommitted items that: have a newer version, weren't included in
// the request.
func (n *Node) FwdPropagate(
	verByKey *transport.PropagateRequest,
) (*transport.PropagateResponse, error) {
	unseen, err := n.store.AllNewerDirty(map[string]uint64(*verByKey))
	if err != nil {
		return nil, err
	}
	return makePropagateResponse(unseen), nil
}

func makePropagateResponse(items []*store.Item) *transport.PropagateResponse {
	response := transport.PropagateResponse{}

	for _, item := range items {
		response[item.Key] = append(response[item.Key], transport.ValueVersion{
			Value:   item.Value,
			Version: item.Version,
		})
	}

	return &response
}
