package swift

import (
	"bytes"
	"crypto/sha256"
	"fmt"
	"slices"

	"github.com/imdea-software/swiftpaxos/state"
)

type SHash struct {
	H [32]byte
}

type HashNode struct {
	id       CommandId
	next     *HashNode
	previous *HashNode
}

type UpdateEntry struct {
	hash   []SHash
	seqnum int
}

// TODO: commutative reads

type HashLog struct {
	// seqnum of the highest synced command
	synced int
	// hash of the highest synced command
	syncedHash SHash
	// head and tail of the linked list of pending commands
	pendingHead *HashNode
	pendingTail *HashNode
	// hash of the last command in the log
	hash SHash
	// mapping from cmdIds to nodes
	nodes map[CommandId]*HashNode
	// mapping from yet-to-be-synced commands to seqnums and hashes
	// this is for the cases when a command is updated before being appended
	pendingUpd map[CommandId]*UpdateEntry
}

func (n *HashNode) String() string {
	if n == nil {
		return "[]"
	}
	return n.id.String() + " -> " + n.next.String()
}

func NewHashLog() *HashLog {
	return &HashLog{
		synced:     -1,
		nodes:      make(map[CommandId]*HashNode),
		pendingUpd: make(map[CommandId]*UpdateEntry),
	}
}

func (l *HashLog) Append(_ state.Command, cmdId CommandId) SHash {
	if upd, exists := l.pendingUpd[cmdId]; exists {
		delete(l.pendingUpd, cmdId)
		l.update(cmdId, upd.seqnum, upd.hash[0], false)
		return upd.hash[0]
	}

	node := &HashNode{
		id: cmdId,
	}
	l.nodes[cmdId] = node

	if l.pendingHead == nil {
		l.pendingHead = node
		l.hash = SHash{l.chain(l.syncedHash.H, l.synced >= 0, cmdId)}
		return l.hash
	}
	if l.pendingTail == nil {
		l.pendingTail = node
		node.previous = l.pendingHead
		l.pendingHead.next = node
	} else {
		l.pendingTail.next = node
		node.previous = l.pendingTail
		l.pendingTail = node
	}
	l.hash = SHash{hash(l.hash.H, cmdId)}
	return l.hash
}

func (l *HashLog) Update(cmdId CommandId, s int, h SHash) {
	l.update(cmdId, s, h, true)
}

func (l *HashLog) String() string {
	s := fmt.Sprintf("%v, syncedHash: %v\n", l.synced, l.syncedHash)
	s += l.pendingHead.String() + "\n"
	return s + fmt.Sprintf("hash: %v", l.hash)
}

func (l *HashLog) update(cmdId CommandId, s int, h SHash, save bool) {
	n, exists := l.nodes[cmdId]
	if !exists && save {
		l.pendingUpd[cmdId] = &UpdateEntry{
			hash:   []SHash{h},
			seqnum: s,
		}
		return
	}
	if exists {
		previous := n.previous
		next := n.next
		if previous != nil {
			previous.next = next
		}
		if next != nil {
			next.previous = previous
		}
		if l.pendingHead == n {
			l.pendingHead = next
		}
		if l.pendingTail == n {
			l.pendingTail = previous
		}
		n.previous = nil
		n.next = nil
		delete(l.nodes, cmdId)
	}
	// TODO: do not update if !exist and s > l.synced but l.syncedHash == h
	if s <= l.synced && !exists {
		return
	}
	if s > l.synced {
		l.synced = s
		l.syncedHash = h
	}
	initial := l.syncedHash.H
	started := l.synced >= 0
	n = l.pendingHead
	for n != nil {
		initial = l.chain(initial, started, n.id)
		started = true
		n = n.next
	}
	l.hash = SHash{initial}
}

// chain is the hash of a path extended by cmdId: the path's hash h if it is
// not empty (started), else the path [cmdId]'s, a hash of the id alone. A
// path's first command is hashed over 8 bytes, every next one over 40 (the
// previous hash and the id): equal path hashes are equal paths (F2), not
// only paths with a common suffix (a chain from the zero hash cannot be told
// from one whose prefix hashes to zero).
func (l *HashLog) chain(h [32]byte, started bool, cmdId CommandId) [32]byte {
	if started {
		return hash(h, cmdId)
	}
	return hashStart(cmdId)
}

// hashStart is the hash of the path [cmdId].
func hashStart(cmdId CommandId) [32]byte {
	bs := make([]byte, 8)
	putId(bs, cmdId)
	return sha256.Sum256(bs)
}

func putId(bs []byte, cmdId CommandId) {
	tmp32 := cmdId.ClientId
	bs[0] = byte(tmp32)
	bs[1] = byte(tmp32 >> 8)
	bs[2] = byte(tmp32 >> 16)
	bs[3] = byte(tmp32 >> 24)
	tmp32 = cmdId.SeqNum
	bs[4] = byte(tmp32)
	bs[5] = byte(tmp32 >> 8)
	bs[6] = byte(tmp32 >> 16)
	bs[7] = byte(tmp32 >> 24)
}

func hash(initial [32]byte, cmdId CommandId) [32]byte {
	bs := make([]byte, 40)
	for i, b := range initial {
		bs[i] = b
	}

	putId(bs[32:], cmdId)

	return sha256.Sum256(bs)
}

// clientChecksum is what a replica sends a client as a command's hashes: the
// hashes of its dependency paths, then a hash of its dependencies (sorted).
// The client's fast path (SHashesEq of the leader's and a fast quorum's) then
// means the paper's condition, a fast quorum pre-accepted the command with
// the leader's dependencies, which the recovery keeps (R1); equal paths alone
// do not give equal dependencies (a follower's path splices in the leader's
// synced prefix, its dependencies follow its own arrival order).
func clientChecksum(hs []SHash, dep []CommandId) []SHash {
	ids := make([]CommandId, len(dep))
	copy(ids, dep)
	slices.SortFunc(ids, cmdIdCmp)
	h := [32]byte{}
	for _, id := range ids {
		h = hash(h, id)
	}
	// a path hash chains from the zero hash over command ids; mark the
	// dependencies' hash apart from those (one more round, over an id no
	// client has)
	h = hash(h, CommandId{ClientId: -1, SeqNum: int32(len(ids))})
	out := make([]SHash, len(hs), len(hs)+1)
	copy(out, hs)
	return append(out, SHash{H: h})
}

// cmdIdCmp is cmdIdLess as a three-way comparison (slices.SortFunc's).
func cmdIdCmp(a, b CommandId) int {
	if cmdIdLess(a, b) {
		return -1
	}
	if cmdIdLess(b, a) {
		return 1
	}
	return 0
}

func cmdIdLess(a, b CommandId) bool {
	return a.ClientId < b.ClientId || (a.ClientId == b.ClientId && a.SeqNum < b.SeqNum)
}

func SHashesEq(hs1 []SHash, hs2 []SHash) bool {
	if len(hs1) != len(hs2) {
		return false
	}

	for _, h := range hs1 {
		eq := false
		for _, g := range hs2 {
			if bytes.Equal(h.H[:], g.H[:]) {
				eq = true
				break
			}
		}
		if !eq {
			return false
		}
	}

	return true
}
