package gryff

import (
  "gryff/src/bloomfilter"
  "gryff/src/dlog"
  "encoding/binary"
  "gryff/src/epaxosproto"
  "gryff/src/fastrpc"
  "gryff/src/genericsmr"
  "gryff/src/genericsmrproto"
  "io"
  "log"
  "math"
  "gryff/src/state"
  "time"
  "gryff/src/gryffproto"
  "sync/atomic"
)

const MAX_DEPTH_DEP = 10
const DS = 5

const COMMIT_GRACE_PERIOD = 10 * 1000000000 //10 seconds (verification workaround (T2): integer constant, was 10 * 1e9)

const BF_K = 4
const BF_M_N = 32.0

// verification workaround (B2-R1): MAX_BATCH as an untyped float constant (float64(MAX_BATCH)
// converts an untyped integer constant to float64, which the pinned Perennial does not step; the
// value, 5000, is exact in float64)
const MAX_BATCH_F = 5000.0

var bf_PT uint32

const DO_CHECKPOINTING = false
const HT_INIT_SIZE = 200000
const CHECKPOINT_PERIOD = 10000

var cpMarker []state.Command
var cpcounter = 0

type Instance struct {
  Cmds           []state.Command
  ballot         int32
  Status         int8
  Seq            int32
  Deps           [DS]int32
  Base           gryffproto.ValTag
  lb             *LeaderBookkeeping
  Index, Lowlink int
  bfilter        *bloomfilter.Bloomfilter
  Slot           int32
  Leader         int32
  // fix (G16): the ballot at which the copy's current value (command, seq, deps, base) was
  // adopted (pre-accepted or accepted), as Paxos's accepted ballot; ballot is the promise
  vbal           int32
}

type instanceId struct {
  replica  int32
  instance int32
}

type RecoveryInstance struct {
  cmds            []state.Command
  status          int8
  seq             int32
  deps            [DS]int32
  base gryffproto.ValTag
  preAcceptCount  int
  leaderResponded bool
  vbal            int32 // fix (G16): the copy's vbal (the ballot at which it adopted the value)
}

type LeaderBookkeeping struct {
  clientProposals   []*genericsmr.Propose
  maxRecvBallot     int32
  prepareOKs        int
  allEqual          bool
  preAcceptOKs      int
  acceptOKs         int
  nacks             int
  originalDeps      [DS]int32
  committedDeps     []int32
  recoveryInst      *RecoveryInstance
  preparing         bool
  tryingToPreAccept bool
  possibleQuorum    []bool
  tpaOKs            int
  committedTime     time.Time
  executedTime      time.Time
  blockStartTime    time.Time
  depReadTime       []time.Time
  numReplicasExecuted int32
  repliedClient bool
}

type ExecuteOverwrite struct {
  K state.Key
  V state.Value
  T *gryffproto.Tag
  Leader int32
  Slot int32
}

type EPaxosRMWHandler struct {
  R *Replica
  prepareChan           chan fastrpc.Serializable
  preAcceptChan         chan fastrpc.Serializable
  acceptChan            chan fastrpc.Serializable
  commitChan            chan fastrpc.Serializable
  commitShortChan       chan fastrpc.Serializable
  prepareReplyChan      chan fastrpc.Serializable
  preAcceptReplyChan    chan fastrpc.Serializable
  preAcceptOKChan       chan fastrpc.Serializable
  acceptReplyChan       chan fastrpc.Serializable
  tryPreAcceptChan      chan fastrpc.Serializable
  tryPreAcceptReplyChan chan fastrpc.Serializable
  executedChan chan fastrpc.Serializable
  preAcceptOKReplyChan chan fastrpc.Serializable
  acceptOKReplyChan chan fastrpc.Serializable
  prepareRPC            uint8
  prepareReplyRPC       uint8
  preAcceptRPC          uint8
  preAcceptReplyRPC     uint8
  preAcceptOKRPC        uint8
  acceptRPC             uint8
  acceptReplyRPC        uint8
  commitRPC             uint8
  commitShortRPC        uint8
  tryPreAcceptRPC       uint8
  tryPreAcceptReplyRPC  uint8
  executedRPC  uint8
  preAcceptOKReplyRPC uint8
  acceptOKReplyRPC uint8
  InstanceSpace         [][]*Instance // the space of all instances (used and not yet used)
  crtInstance           []int32       // highest active instance numbers that this replica knows about
  CommittedUpTo         [DS]int32     // highest committed instance per replica that this replica knows about
  ExecedUpTo            []int32       // instance up to which all commands have been executed (including iteslf)
  exec                  *Exec
  conflicts1            []map[state.Key]map[state.Operation]int32
  maxSeqPerKey1         map[state.Key]map[state.Operation]int32
  conflicts             []map[state.Key]int32
  maxSeqPerKey          map[state.Key]int32
  maxSeq                int32
  latestCPEPaxosRMWHandler       int32
  latestCPInstance      int32
  instancesToRecover    chan *instanceId
  noConflicts bool
  PrevValTag            map[state.Key]gryffproto.ValTag
  preAcceptOKs [][]int
  acceptOKs [][]int
  executeOverwriteChan chan *ExecuteOverwrite
  broadcastOptimizationEnabled bool
}

func NewEPaxosRMWHandler(r *Replica, noConflicts bool, broadcastOptimizationEnabled bool) *EPaxosRMWHandler {
  e := &EPaxosRMWHandler{
    r,
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE*3),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE*3),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE*2),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE),
    make(chan fastrpc.Serializable, genericsmr.CHAN_BUFFER_SIZE),
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    make([][]*Instance, r.N),
    make([]int32, r.N),
    [DS]int32{-1, -1, -1, -1, -1},
    make([]int32, r.N),
    nil,
    make([]map[state.Key]map[state.Operation]int32, r.N),
    make(map[state.Key]map[state.Operation]int32),
    make([]map[state.Key]int32, r.N),
    make(map[state.Key]int32),
    0,
    0,
    -1,
    make(chan *instanceId, genericsmr.CHAN_BUFFER_SIZE),
    noConflicts,
    make(map[state.Key]gryffproto.ValTag),
    make([][]int, r.N),
    make([][]int, r.N),
    make(chan *ExecuteOverwrite, genericsmr.CHAN_BUFFER_SIZE),
    broadcastOptimizationEnabled,
  }

  for i := 0; i < e.R.N; i++ {
    e.InstanceSpace[i] = make([]*Instance, 2*1024*1024)
    e.crtInstance[i] = 0
    e.ExecedUpTo[i] = -1
    e.conflicts1[i] = make(map[state.Key]map[state.Operation]int32,
      HT_INIT_SIZE)
    e.conflicts[i] = make(map[state.Key]int32, HT_INIT_SIZE)
    e.preAcceptOKs[i] = make([]int, 2*1024*1024)
    e.acceptOKs[i] = make([]int, 2*1024*1024)
  }

  for bf_PT = 1; math.Pow(2, float64(bf_PT))/MAX_BATCH_F < BF_M_N; {
    bf_PT++
  }

  e.exec = &Exec{e}

  cpMarker = make([]state.Command, 0)

  //register RPCs
  e.prepareRPC = e.R.RegisterRPC(new(epaxosproto.Prepare), e.prepareChan)
  e.prepareReplyRPC = e.R.RegisterRPC(new(gryffproto.PrepareReply), e.prepareReplyChan)
  e.preAcceptRPC = e.R.RegisterRPC(new(gryffproto.PreAccept), e.preAcceptChan)
  e.preAcceptReplyRPC = e.R.RegisterRPC(new(gryffproto.PreAcceptReply), e.preAcceptReplyChan)
  e.preAcceptOKRPC = e.R.RegisterRPC(new(epaxosproto.PreAcceptOK), e.preAcceptOKChan)
  e.acceptRPC = e.R.RegisterRPC(new(gryffproto.EAccept), e.acceptChan)
  e.acceptReplyRPC = e.R.RegisterRPC(new(epaxosproto.AcceptReply), e.acceptReplyChan)
  e.commitRPC = e.R.RegisterRPC(new(gryffproto.ECommit), e.commitChan)
  e.commitShortRPC = e.R.RegisterRPC(new(epaxosproto.CommitShort), e.commitShortChan)
  e.tryPreAcceptRPC = e.R.RegisterRPC(new(epaxosproto.TryPreAccept), e.tryPreAcceptChan)
  e.tryPreAcceptReplyRPC = e.R.RegisterRPC(new(epaxosproto.TryPreAcceptReply), e.tryPreAcceptReplyChan)
  e.executedRPC = e.R.RegisterRPC(new(gryffproto.Executed), e.executedChan)
  e.preAcceptOKReplyRPC = e.R.RegisterRPC(new(gryffproto.PreAcceptOKReply),
      e.preAcceptOKReplyChan)
  e.acceptOKReplyRPC = e.R.RegisterRPC(new(gryffproto.AcceptOKReply),
      e.acceptOKReplyChan)

  dlog.Printf("PrepareRPC: %d\n", e.prepareRPC)
  dlog.Printf("PrepareReplyRPC: %d\n", e.prepareReplyRPC)
  dlog.Printf("PreAcceptRPC: %d\n", e.preAcceptRPC)
  dlog.Printf("PreAcceptReplyRPC: %d\n", e.preAcceptReplyRPC)
  dlog.Printf("PreAcceptOKRPC: %d\n", e.preAcceptOKRPC)
  dlog.Printf("AcceptRPC: %d\n", e.acceptRPC)
  dlog.Printf("AcceptReplyRPC: %d\n", e.acceptReplyRPC)
  dlog.Printf("CommitRPC: %d\n", e.commitRPC)
  dlog.Printf("CommitShortRPC: %d\n", e.commitShortRPC)
  dlog.Printf("TryPreAcceptRPC: %d\n", e.tryPreAcceptRPC)
  dlog.Printf("TryPreAcceptReplyRPC: %d\n", e.tryPreAcceptReplyRPC)
  dlog.Printf("ExecutedRPC: %d\n", e.executedRPC)
  dlog.Printf("PreAcceptOKReplyChan: %d\n", e.preAcceptOKReplyRPC)
  dlog.Printf("AcceptOKReplyChan: %d\n", e.acceptOKReplyRPC)
  // verification workaround (B-R7): the executor goroutine is started by NewReplica once the
  // replica holds this handler (it reads only fields set before; a later start is one of the
  // schedules the earlier one allowed)

  return e
}

//append a log entry to stable storage
func (e *EPaxosRMWHandler) recordInstanceMetadata(inst *Instance) {
  if !e.R.Durable {
    return
  }

  var b [9 + DS*4]byte
  binary.LittleEndian.PutUint32(b[0:4], uint32(inst.ballot))
  b[4] = byte(inst.Status)
  binary.LittleEndian.PutUint32(b[5:9], uint32(inst.Seq))
  l := 9
  for _, dep := range inst.Deps {
    binary.LittleEndian.PutUint32(b[l:l+4], uint32(dep))
    l += 4
  }
  e.R.StableStore.Write(b[:])
}

//write a sequence of commands to stable storage
func (e *EPaxosRMWHandler) recordCommands(cmds []state.Command) {
  if !e.R.Durable {
    return
  }

  if cmds == nil {
    return
  }
  for i := 0; i < len(cmds); i++ {
    cmds[i].Marshal(io.Writer(e.R.StableStore))
  }
}

//sync with the stable store
func (e *EPaxosRMWHandler) sync() {
  if !e.R.Durable {
    return
  }

  e.R.StableStore.Sync()
}

var conflicted, weird, slow, happy int
func (e *EPaxosRMWHandler) Loop(slowClockChan chan bool) {
  select {
    case <-slowClockChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      if e.R.Beacon {
        for q := int32(0); q < int32(e.R.N); q++ {
          if q == e.R.Id {
            continue
          }
          e.R.SendBeacon(q)
        }
      }
      e.R.mtx.Unlock()
      break
    case beacon := <-e.R.BeaconChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      dlog.Printf("Received Beacon from replica %d with timestamp %d\n",
          beacon.Rid, beacon.Timestamp)
      e.R.ReplyBeacon(beacon)
      e.R.mtx.Unlock()
      break
    case <-e.R.DoneAdaptingChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      for i := 0; i < e.R.N - 1; i++ { 
        e.R.myPreferredPeerOrder[i + 1] = e.R.PreferredPeerOrder[i]
      }
      e.R.mtx.Unlock()
      break
    case readS := <-e.R.readChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      read := readS.Obj.(*gryffproto.Read)
      e.R.resolveRead(read) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      // got Read message
      e.R.handleRead(read)
      e.R.mtx.Unlock()
      break
    case writeS := <-e.R.writeChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      write := writeS.Obj.(*gryffproto.Write)
      e.R.resolveWrite(write) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      // got Write message
      e.R.handleWrite(write)
      e.R.mtx.Unlock()
      break
    case rmwS := <-e.R.rmwChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      rmw := rmwS.Obj.(*gryffproto.RMW)
      e.R.resolveRMW(rmw) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      e.HandleRMW(rmw)
      e.R.mtx.Unlock()
      break
    case write1ProxiedS := <-e.R.write1ChanProxied:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      write1Proxied := write1ProxiedS.(*gryffproto.Write1Proxied)
      e.R.resolveWrite1(write1Proxied) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a Write  message
      e.R.handleWrite1Proxied(write1Proxied)
      e.R.mtx.Unlock()
      break
    case write2ProxiedS := <-e.R.write2ChanProxied:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      write2Proxied := write2ProxiedS.(*gryffproto.Write2Proxied)
      e.R.resolveWrite2(write2Proxied) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a Write  message
      e.R.handleWrite2Proxied(write2Proxied)
      e.R.mtx.Unlock()
      break
    case read1ProxiedS := <-e.R.read1ChanProxied:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      read1Proxied := read1ProxiedS.(*gryffproto.Read1Proxied)
      e.R.resolveRead1(read1Proxied) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a Read  message
      e.R.handleRead1Proxied(read1Proxied)
      e.R.mtx.Unlock()
      break
    case read2ProxiedS := <-e.R.read2ChanProxied:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      read2Proxied := read2ProxiedS.(*gryffproto.Read2Proxied)
      e.R.resolveRead2(read2Proxied) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a Read  message
      e.R.handleRead2Proxied(read2Proxied)
      e.R.mtx.Unlock()
      break
    case write1ReplyS := <-e.R.write1ReplyChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      write1Reply := write1ReplyS.(*gryffproto.Write1Reply)
      e.R.resolveWrite1Reply(write1Reply) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a Write  message
      e.R.handleWrite1Reply(write1Reply)
      e.R.mtx.Unlock()
      break
    case write1ReplyS := <-e.R.write1TimeoutChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      write1Reply := write1ReplyS.(*gryffproto.Write1Reply)
      // got a Write1 timeout message
      e.R.handleWrite1Timeout(write1Reply)
      e.R.mtx.Unlock()
      break
    case write2S := <-e.R.write2ConcurrentTimeoutChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      write2 := write2S.(*gryffproto.Write2Proxied)
      // got a concurrent Write2 timeout message
      e.R.handleWrite2ConcurrentTimeout(write2)
      e.R.mtx.Unlock()
      break
    case write2ReplyS := <-e.R.write2ReplyChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      write2Reply := write2ReplyS.(*gryffproto.Write2Reply)
      e.R.resolveWrite2Reply(write2Reply) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a Write  message
      e.R.handleWrite2Reply(write2Reply)
      e.R.mtx.Unlock()
      break
    case read1ReplyS := <-e.R.read1ReplyChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      read1Reply := read1ReplyS.(*gryffproto.Read1Reply)
      e.R.resolveRead1Reply(read1Reply) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a Read  message
      e.R.handleRead1Reply(read1Reply)
      e.R.mtx.Unlock()
      break
    case read2ReplyS := <-e.R.read2ReplyChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      read2Reply := read2ReplyS.(*gryffproto.Read2Reply)
      e.R.resolveRead2Reply(read2Reply) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a Read  message
      e.R.handleRead2Reply(read2Reply)
      e.R.mtx.Unlock()
      break
    case <-e.R.forceWriteChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      e.R.resolveForceWrite() // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      e.R.handleForceWrite()
      e.R.mtx.Unlock()
      break
    case prepareS := <-e.prepareChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      prepare := prepareS.(*epaxosproto.Prepare)
      e.R.resolvePrepare(prepare) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a Prepare message
      dlog.Printf("Received Prepare for instance %d.%d\n", prepare.Replica, prepare.Instance)
      e.handlePrepare(prepare)
      e.R.mtx.Unlock()
      break
    case preAcceptS := <-e.preAcceptChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      preAccept := preAcceptS.(*gryffproto.PreAccept)
      e.R.resolvePreAccept(preAccept) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a PreAccept message
      dlog.Printf("Received PreAccept for instance %d.%d\n", preAccept.LeaderId, preAccept.Instance)
      e.handlePreAccept(preAccept)
      e.R.mtx.Unlock()
      break
    case acceptS := <-e.acceptChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      accept := acceptS.(*gryffproto.EAccept)
      e.R.resolveAccept(accept) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got an Accept message
      dlog.Printf("Received Accept for instance %d.%d\n", accept.LeaderId, accept.Instance)
      e.handleAccept(accept)
      e.R.mtx.Unlock()
      break
    case commitS := <-e.commitChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      commit := commitS.(*gryffproto.ECommit)
      e.R.resolveCommit(commit) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a Commit message
      dlog.Printf("Received Commit for instance %d.%d\n", commit.LeaderId, commit.Instance)
      e.handleCommit(commit)
      e.R.mtx.Unlock()
      break
    case commitS := <-e.commitShortChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      commit := commitS.(*epaxosproto.CommitShort)
      //got a Commit message
      dlog.Printf("Received Commit for instance %d.%d\n", commit.LeaderId, commit.Instance)
      e.handleCommitShort(commit)
      e.R.mtx.Unlock()
      break
    case prepareReplyS := <-e.prepareReplyChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      prepareReply := prepareReplyS.(*gryffproto.PrepareReply)
      e.R.resolvePrepareReply(prepareReply) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a Prepare reply
      dlog.Printf("Received PrepareReply for instance %d.%d\n", prepareReply.Replica, prepareReply.Instance)
      e.handlePrepareReply(prepareReply)
      e.R.mtx.Unlock()
      break
    case preAcceptReplyS := <-e.preAcceptReplyChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      preAcceptReply := preAcceptReplyS.(*gryffproto.PreAcceptReply)
      e.R.resolvePreAcceptReply(preAcceptReply) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a PreAccept reply
      dlog.Printf("Received PreAcceptReply for instance %d.%d\n", preAcceptReply.Replica, preAcceptReply.Instance)
      e.handlePreAcceptReply(preAcceptReply)
      e.R.mtx.Unlock()
      break
    case preAcceptOKS := <-e.preAcceptOKChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      preAcceptOK := preAcceptOKS.(*epaxosproto.PreAcceptOK)
      e.R.resolvePreAcceptOK(preAcceptOK) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got a PreAccept reply
      dlog.Printf("Received PreAcceptOK for instance %d.%d\n", e.R.Id, preAcceptOK.Instance)
      e.handlePreAcceptOK(preAcceptOK)
      e.R.mtx.Unlock()
      break
    case acceptReplyS := <-e.acceptReplyChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      acceptReply := acceptReplyS.(*epaxosproto.AcceptReply)
      e.R.resolveAcceptReply(acceptReply) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      //got an Accept reply
      dlog.Printf("Received AcceptReply for instance %d.%d\n", acceptReply.Replica, acceptReply.Instance)
      e.handleAcceptReply(acceptReply)
      e.R.mtx.Unlock()
      break
    case tryPreAcceptS := <-e.tryPreAcceptChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      tryPreAccept := tryPreAcceptS.(*gryffproto.TryPreAccept)
      dlog.Printf("Received TryPreAccept for instance %d.%d\n", tryPreAccept.Replica, tryPreAccept.Instance)
      e.handleTryPreAccept(tryPreAccept)
      e.R.mtx.Unlock()
      break
    case tryPreAcceptReplyS := <-e.tryPreAcceptReplyChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      tryPreAcceptReply := tryPreAcceptReplyS.(*epaxosproto.TryPreAcceptReply)
      dlog.Printf("Received TryPreAcceptReply for instance %d.%d\n", tryPreAcceptReply.Replica, tryPreAcceptReply.Instance)
      e.handleTryPreAcceptReply(tryPreAcceptReply)
      e.R.mtx.Unlock()
      break
    case executedS := <-e.executedChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      executed := executedS.(*gryffproto.Executed)
      e.R.resolveExecuted(executed) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      dlog.Printf("Received Executed for instance %d.%d\n", executed.Replica,
          executed.Instance)
      e.handleExecuted(executed)
      e.R.mtx.Unlock()
      break
    case preAcceptOKReplyS := <-e.preAcceptOKReplyChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      preAcceptOKReply := preAcceptOKReplyS.(*gryffproto.PreAcceptOKReply)
      dlog.Printf("Received PreAcceptOKReply for instance %d.%d.\n",
          preAcceptOKReply.Replica, preAcceptOKReply.Instance)
      e.handlePreAcceptOKReply(preAcceptOKReply)
      e.R.mtx.Unlock()
      break
    case acceptOKReplyS := <-e.acceptOKReplyChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      acceptOKReply := acceptOKReplyS.(*gryffproto.AcceptOKReply)
      dlog.Printf("Received AcceptOKReply for instance %d.%d.\n",
          acceptOKReply.Replica, acceptOKReply.Instance)
      e.handleAcceptOKReply(acceptOKReply)
      e.R.mtx.Unlock()
      break
    case executeOverwrite := <-e.executeOverwriteChan:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      e.R.resolveExecuteOverwrite(executeOverwrite) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      e.executeOverwrite(executeOverwrite)
      e.R.mtx.Unlock()
      break
    case <-e.R.OnClientConnect:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      log.Printf("weird %d; conflicted %d; slow %d; happy %d\n", weird, conflicted, slow, happy)
      weird, conflicted, slow, happy = 0, 0, 0, 0
      e.R.mtx.Unlock()
      break
    case iid := <-e.instancesToRecover:
      e.R.mtx.Lock() // fix (G2): the run loop handles each message under the replica's lock
      e.R.resolveRecover(iid.replica, iid.instance) // verification workaround (ghost code, D9): the event, as the trace prophecy's words
      e.startRecoveryForInstance(iid.replica, iid.instance)
      e.R.mtx.Unlock()
      break
  }
}

func (e *EPaxosRMWHandler) HandleRMW(rmw *gryffproto.RMW) {
  dlog.Printf("Handling RMW %d.%d.\n", rmw.ClientId, rmw.RequestId)
  propose := &genericsmr.Propose{
    &genericsmrproto.Propose{
      rmw.RequestId,
      state.Command{
        state.CAS,
        rmw.K,
        rmw.NewValue,
        rmw.OldValue,
      },
      0,
    },
    e.R.GetClientWriter(rmw.ClientId),
  }
  e.handlePropose(propose)
}

/***********************************
   Command execution thread        *
************************************/

func (e *EPaxosRMWHandler) executeCommands() {
  const SLEEP_TIME_NS = 1000000 // verification workaround (T2): integer constant, was 1e6
  problemInstance := make([]int32, e.R.N)
  timeout := make([]uint64, e.R.N)
  for q := 0; q < e.R.N; q++ {
    problemInstance[q] = -1
    timeout[q] = 0
  }

  for !e.R.Shutdown {
    // fix (G2): the executor runs under the replica's lock (the run loop's handlers create and
    // update the instances it reads and writes); it releases it while it sleeps
    e.R.mtx.Lock()
    executed := false
    for q := 0; q < e.R.N; q++ {
      inst := int32(0)
      for inst = e.ExecedUpTo[q] + 1; inst < e.crtInstance[q]; inst++ {
        if e.InstanceSpace[q][inst] != nil && e.InstanceSpace[q][inst].Status == epaxosproto.EXECUTED {
          dlog.Printf("[%d.%d] Already execed via dependent instance (ExecedUpTo=%d).\n", q, inst, e.ExecedUpTo[q])
          if inst == e.ExecedUpTo[q]+1 {
            e.ExecedUpTo[q] = inst
          }
          continue
        }
        if e.InstanceSpace[q][inst] == nil || e.InstanceSpace[q][inst].Status != epaxosproto.COMMITTED {
          if inst == problemInstance[q] {
            timeout[q] += SLEEP_TIME_NS
            if timeout[q] >= COMMIT_GRACE_PERIOD {
              dlog.Printf("crtInstance=%d,ExecutedUpTo=%d,problemInstance=%d,timeout=%d,q=%d,inst=%d,instspace=%+v.\n",
                e.crtInstance[q], e.ExecedUpTo[q], problemInstance[q], timeout[q], q, inst, e.InstanceSpace[q][inst])
              e.instancesToRecover <- &instanceId{int32(q), inst}
              timeout[q] = 0
            }
          } else {
            problemInstance[q] = inst
            timeout[q] = 0
          }
          if e.InstanceSpace[q][inst] == nil {
            continue
          }
          break
        }
        if e.InstanceSpace[q][inst].lb != nil {
          dlog.Printf("[%d.%d] Trying to execute at time %d.\n", q, inst, time.Now().Sub(e.InstanceSpace[q][inst].lb.committedTime))
        }
        if ok := e.exec.executeCommand(int32(q), inst); ok {
          executed = true
          if inst == e.ExecedUpTo[q]+1 {
            e.ExecedUpTo[q] = inst
          }
        }
      }
    }
    e.R.mtx.Unlock()
    if !executed {
      time.Sleep(SLEEP_TIME_NS)
    }
    //dlog.Printf("ExecedUpTo=%v, crtInstance=%v.\n", e.ExecedUpTo, e.crtInstance)
  }
}

/* Ballot helper functions */

func (e *EPaxosRMWHandler) makeUniqueBallot(ballot int32) int32 {
  return (ballot << 4) | e.R.Id
}

func (e *EPaxosRMWHandler) makeBallotLargerThan(ballot int32) int32 {
  return e.makeUniqueBallot((ballot >> 4) + 1)
}

func isInitialBallot(ballot int32) bool {
  return (ballot >> 4) == 0
}

func replicaIdFromBallot(ballot int32) int32 {
  return ballot & 15
}

/**********************************************************************
                    inter-replica communication
***********************************************************************/

func (e *EPaxosRMWHandler) replyPrepare(replicaId int32, reply *gryffproto.PrepareReply) {
  e.R.SendMsg(replicaId, e.prepareReplyRPC, reply)
}

func (e *EPaxosRMWHandler) replyPreAccept(replicaId int32, reply *gryffproto.PreAcceptReply) {
  e.R.SendMsg(replicaId, e.preAcceptReplyRPC, reply)
}

func (e *EPaxosRMWHandler) replyAccept(replicaId int32, reply *epaxosproto.AcceptReply) {
  e.R.SendMsg(replicaId, e.acceptReplyRPC, reply)
}

func (e *EPaxosRMWHandler) replyTryPreAccept(replicaId int32, reply *epaxosproto.TryPreAcceptReply) {
  e.R.SendMsg(replicaId, e.tryPreAcceptReplyRPC, reply)
}

func (e *EPaxosRMWHandler) replyExecuted(replicaId int32,
    reply *gryffproto.Executed) {
  e.R.SendMsg(replicaId, e.executedRPC, reply)
}

func (e *EPaxosRMWHandler) bcastPrepare(replica int32, instance int32, ballot int32) {
  defer func() {
    if err := recover(); err != nil {
      dlog.Println("Prepare bcast failed:", err)
    }
  }()
  args := &epaxosproto.Prepare{e.R.Id, replica, instance, ballot}

  n := e.R.N - 1
  if e.R.Thrifty {
    n = e.R.N / 2
  }
  q := e.R.Id
  for sent := 0; sent < n; {
    q = (q + 1) % int32(e.R.N)
    if q == e.R.Id {
      dlog.Println("Not enough replicas alive!")
      break
    }
    if !e.R.Alive[q] {
      continue
    }
    e.R.SendMsg(q, e.prepareRPC, args)
    sent++
  }
}

var pa gryffproto.PreAccept

func (e *EPaxosRMWHandler) bcastPreAccept(replica int32, instance int32, ballot int32, cmds []state.Command, seq int32, deps [DS]int32, base gryffproto.ValTag) {
  defer func() {
    if err := recover(); err != nil {
      dlog.Println("PreAccept bcast failed:", err)
    }
  }()
  pa.LeaderId = e.R.Id
  pa.Replica = replica
  pa.Instance = instance
  pa.Ballot = ballot
  pa.Command = cmds
  pa.Seq = seq
  pa.Deps = deps
  pa.Base = base // fix (G20): the PreAccept carries the proposer's base (handlePreAccept compares with it)
  args := &pa

  n := e.R.N - 1
  if e.R.Thrifty {
    n = e.R.N / 2
  }

  sent := 0
  for q := 0; q < e.R.N-1; q++ {
    if !e.R.Alive[e.R.PreferredPeerOrder[q]] {
      continue
    }
    dlog.Printf("[%d.%d] Sending PreAccept to %d (%s).\n", replica, instance, e.R.PreferredPeerOrder[q], e.R.PeerAddrList[e.R.PreferredPeerOrder[q]])
    e.R.SendMsg(e.R.PreferredPeerOrder[q], e.preAcceptRPC, args)
    sent++
    if sent >= n {
      break
    }
  }
}

var tpa gryffproto.TryPreAccept

func (e *EPaxosRMWHandler) bcastTryPreAccept(replica int32, instance int32, ballot int32, cmds []state.Command, seq int32, deps [DS]int32, base gryffproto.ValTag) {
  defer func() {
    if err := recover(); err != nil {
      dlog.Println("PreAccept bcast failed:", err)
    }
  }()
  tpa.LeaderId = e.R.Id
  tpa.Replica = replica
  tpa.Instance = instance
  tpa.Ballot = ballot
  tpa.Command = cmds
  tpa.Seq = seq
  tpa.Deps = deps
  tpa.Base = base
  args := &pa

  for q := int32(0); q < int32(e.R.N); q++ {
    if q == e.R.Id {
      continue
    }
    if !e.R.Alive[q] {
      continue
    }
    e.R.SendMsg(q, e.tryPreAcceptRPC, args)
  }
}

var ea gryffproto.EAccept

func (e *EPaxosRMWHandler) bcastAccept(replica int32, instance int32, ballot int32, cmds []state.Command, seq int32, deps [DS]int32, base gryffproto.ValTag) {
  defer func() {
    if err := recover(); err != nil {
      dlog.Println("Accept bcast failed:", err)
    }
  }()

  ea.LeaderId = e.R.Id
  ea.Replica = replica
  ea.Instance = instance
  ea.Ballot = ballot
  ea.Count = int32(len(cmds))
  ea.Command = cmds // fix (G19): the Accept carries the command (handleAccept stores it)
  ea.Seq = seq
  ea.Deps = deps
  ea.Base = base // fix (G3): the Accept carries the instance's base (handleAccept stores it)
  args := &ea

  n := e.R.N - 1
  if e.R.Thrifty {
    n = e.R.N / 2
  }

  sent := 0
  for q := 0; q < e.R.N-1; q++ {
    if !e.R.Alive[e.R.PreferredPeerOrder[q]] {
      continue
    }
    e.R.SendMsg(e.R.PreferredPeerOrder[q], e.acceptRPC, args)
    sent++
    if sent >= n {
      break
    }
  }
}

var ec gryffproto.ECommit
var ecs epaxosproto.CommitShort

func (e *EPaxosRMWHandler) bcastCommit(replica int32, instance int32, cmds []state.Command, seq int32, deps [DS]int32, base gryffproto.ValTag) {
  defer func() {
    if err := recover(); err != nil {
      dlog.Println("Commit bcast failed:", err)
    }
  }()
  ec.LeaderId = e.R.Id
  ec.Replica = replica
  ec.Instance = instance
  ec.Command = cmds
  ec.Seq = seq
  ec.Deps = deps
  ec.Base = base
  args := &ec
  ecs.LeaderId = e.R.Id
  ecs.Replica = replica
  ecs.Instance = instance
  ecs.Count = int32(len(cmds))
  ecs.Seq = seq
  ecs.Deps = deps
  argsShort := &ecs

  sent := 0
  for q := 0; q < e.R.N-1; q++ {
    if !e.R.Alive[e.R.PreferredPeerOrder[q]] {
      continue
    }
    if e.R.Exec || e.R.Thrifty && sent >= e.R.N/2 {
      dlog.Printf("[%d.%d] Sending Commit to %d (%s).\n", replica, instance, e.R.PreferredPeerOrder[q], e.R.PeerAddrList[e.R.PreferredPeerOrder[q]])
      e.R.SendMsg(e.R.PreferredPeerOrder[q], e.commitRPC, args)
    } else {
      dlog.Printf("[%d.%d] Sending CommitShort to %d (%s).\n", replica, instance, e.R.PreferredPeerOrder[q], e.R.PeerAddrList[e.R.PreferredPeerOrder[q]])
      e.R.SendMsg(e.R.PreferredPeerOrder[q], e.commitShortRPC, argsShort)
      sent++
    }  
  }
}

var paokr gryffproto.PreAcceptOKReply

func (e *EPaxosRMWHandler) bcastPreAcceptOKReply(replica int32, instance int32) {
  defer func() {
    if err := recover(); err != nil {
      dlog.Println("PreAcceptOKReply bcast failed:", err)
    }
  }()

  paokr.Replica = replica
  paokr.Instance = instance

  for q := 0; q < e.R.N - 1; q++ {
    if !e.R.Alive[e.R.PreferredPeerOrder[q]] {
      continue
    }
    e.R.SendMsg(e.R.PreferredPeerOrder[q], e.preAcceptOKReplyRPC, &paokr)
  }
}

var aokr gryffproto.AcceptOKReply

func (e *EPaxosRMWHandler) bcastAcceptOKReply(replica int32, instance int32) {
  defer func() {
    if err := recover(); err != nil {
      dlog.Println("AcceptOKReply bcast failed:", err)
    }
  }()

  aokr.Replica = replica
  aokr.Instance = instance

  for q := 0; q < e.R.N - 1; q++ {
    if !e.R.Alive[e.R.PreferredPeerOrder[q]] {
      continue
    }
    e.R.SendMsg(e.R.PreferredPeerOrder[q], e.acceptOKReplyRPC, &aokr)
  }
}



/******************************************************************
               Helper functions
*******************************************************************/

func (e *EPaxosRMWHandler) clearHashtables() {
  for q := 0; q < e.R.N; q++ {
    e.conflicts1[q] = make(map[state.Key]map[state.Operation]int32, HT_INIT_SIZE)
    e.conflicts[q] = make(map[state.Key]int32, HT_INIT_SIZE)
  }
}

func (e *EPaxosRMWHandler) updateCommitted(replica int32) {
  for e.InstanceSpace[replica][e.CommittedUpTo[replica]+1] != nil &&
    (e.InstanceSpace[replica][e.CommittedUpTo[replica]+1].Status == epaxosproto.COMMITTED ||
      e.InstanceSpace[replica][e.CommittedUpTo[replica]+1].Status == epaxosproto.EXECUTED) {
    e.CommittedUpTo[replica] = e.CommittedUpTo[replica] + 1
    dlog.Printf("Committed up to %d.%d.\n", replica, e.CommittedUpTo[replica])
  }
}

func (e *EPaxosRMWHandler) updateConflicts(cmds []state.Command, replica int32, instance int32, seq int32) {
  if !e.noConflicts {
    for i := 0; i < len(cmds); i++ {
      opMapDep, ok := e.conflicts1[replica][cmds[i].K]
      if !ok {
        opMapDep = make(map[state.Operation]int32)
      }
      opMapSeq, ok := e.maxSeqPerKey1[cmds[i].K]
      if !ok {
        opMapSeq = make(map[state.Operation]int32)
      }

      allOpTypes := state.AllOpTypes()
      for j := 0; j < len(allOpTypes); j++ {
        if state.OpTypesConflict(cmds[i].Op, allOpTypes[j]) {
          highestInterf, ok := opMapDep[allOpTypes[j]]
          if !ok || highestInterf < instance {
            opMapDep[allOpTypes[j]] = instance
          }
          maxSeq, ok := opMapSeq[allOpTypes[j]]
          if !ok || maxSeq < seq {
            opMapSeq[allOpTypes[j]] = seq
          }
        }
      }
    
      e.conflicts1[replica][cmds[i].K] = opMapDep
      e.maxSeqPerKey1[cmds[i].K] = opMapSeq
    }
  }
  e.R.Stats.Max("conflicts_map_size", len(e.conflicts1[replica]))
}

func (e *EPaxosRMWHandler) updateAttributes(cmds []state.Command, seq int32, deps [DS]int32, replica int32, instance int32) (int32, [DS]int32, bool) {
  changed := false
  if !e.noConflicts {
    for q := 0; q < e.R.N; q++ {
      if e.R.Id != replica && int32(q) == replica {
        continue
      }
      for i := 0; i < len(cmds); i++ {
        keyMap, ok := e.conflicts1[q][cmds[i].K]
        if ok {
          highestInterf, ok := keyMap[cmds[i].Op]
          if ok && highestInterf > deps[q] {
            deps[q] = highestInterf
            if seq <= e.InstanceSpace[q][highestInterf].Seq {
              seq = e.InstanceSpace[q][highestInterf].Seq + 1
            }
            changed = true
          }
        }
      }
    }

    for i := 0; i < len(cmds); i++ {
      keyMap, ok := e.maxSeqPerKey1[cmds[i].K]
      if ok {
        maxSeq, ok := keyMap[cmds[i].Op]
        if ok && seq <= maxSeq {
          seq = maxSeq + 1
          changed = true
        }
      }
    }
  }
  e.R.Stats.Max("conflicts_map_size", len(e.conflicts1[replica]))
  return seq, deps, changed
}

/*func (e *EPaxosRMWHandler) updateConflicts(cmds []state.Command, replica int32, instance int32, seq int32) {
  for i := 0; i < len(cmds); i++ {
    if d, present := e.conflicts[replica][cmds[i].K]; present {
      if d < instance {
        e.conflicts[replica][cmds[i].K] = instance
      }
    } else {
            e.conflicts[replica][cmds[i].K] = instance
        }
    if s, present := e.maxSeqPerKey[cmds[i].K]; present {
      if s < seq {
        e.maxSeqPerKey[cmds[i].K] = seq
      }
    } else {
      e.maxSeqPerKey[cmds[i].K] = seq
    }
  }
}

func (e *EPaxosRMWHandler) updateAttributes(cmds []state.Command, seq int32, deps [DS]int32, replica int32, instance int32) (int32, [DS]int32, bool) {
  changed := false
  for q := 0; q < e.R.N; q++ {
    if e.R.Id != replica && int32(q) == replica {
      continue
    }
    for i := 0; i < len(cmds); i++ {
      if d, present := (e.conflicts[q])[cmds[i].K]; present {
        if d > deps[q] {
          deps[q] = d
          if seq <= e.InstanceSpace[q][d].Seq {
            seq = e.InstanceSpace[q][d].Seq + 1
          }
          changed = true
          break
        }
      }
    }
  }
  for i := 0; i < len(cmds); i++ {
    if s, present := e.maxSeqPerKey[cmds[i].K]; present {
      if seq <= s {
        changed = true
        seq = s + 1
      }
    }
  }

  return seq, deps, changed
}*/

func (e *EPaxosRMWHandler) mergeAttributes(seq1 int32, deps1 [DS]int32, seq2 int32, deps2 [DS]int32) (int32, [DS]int32, bool) {
  equal := true
  if seq1 != seq2 {
    dlog.Printf("[%d.%d] My seq %d not equal to other seq %d.\n", e.R.Id, seq1, seq1, seq2)
    equal = false
    if seq2 > seq1 {
      seq1 = seq2
    }
  }
  for q := 0; q < e.R.N; q++ {
    if int32(q) == e.R.Id {
      continue
    }
    if deps1[q] != deps2[q] {
      dlog.Printf("[%d.%d] My deps for %d not equal to %d's deps.\n", e.R.Id, seq1, seq1, q)
      equal = false
      if deps2[q] > deps1[q] {
        deps1[q] = deps2[q]
      }
    }
  }
  return seq1, deps1, equal
}

func equal(deps1 *[DS]int32, deps2 *[DS]int32) bool {
  for i := 0; i < len(deps1); i++ {
    if deps1[i] != deps2[i] {
      return false
    }
  }
  return true
}

func bfFromCommands(cmds []state.Command) *bloomfilter.Bloomfilter {
  if cmds == nil {
    return nil
  }

  bf := bloomfilter.NewPowTwo(bf_PT, BF_K)

  for i := 0; i < len(cmds); i++ {
    bf.AddUint64(uint64(cmds[i].K))
  }

  return bf
}

/**********************************************************************

                            PHASE 1

***********************************************************************/

func (e *EPaxosRMWHandler) handlePropose(propose *genericsmr.Propose) {
  //TODO!! Handle client retries

  batchSize := len(e.R.ProposeChan) + 1
  if batchSize > MAX_BATCH {
    batchSize = MAX_BATCH
  }

  instNo := e.crtInstance[e.R.Id]
  e.crtInstance[e.R.Id]++

  dlog.Printf("Starting instance %d\n", instNo)
  dlog.Printf("Batching %d\n", batchSize)


  cmds := make([]state.Command, batchSize)
  proposals := make([]*genericsmr.Propose, batchSize)
  gooseCopy8 := propose.Command // verification workaround (T1): copy through a local
  cmds[0] = gooseCopy8
  proposals[0] = propose
  for i := 1; i < batchSize; i++ {
    prop := <-e.R.ProposeChan
    dlog.Printf("[%d.%d] Starting instance for command %d.\n", e.R.Id, instNo, prop.CommandId)
    gooseCopy2 := prop.Command // verification workaround (T1): copy through a local
    cmds[i] = gooseCopy2
    proposals[i] = prop
  }

  e.startPhase1(e.R.Id, instNo, 0, proposals, cmds, batchSize)
}

func (e *EPaxosRMWHandler) startPhase1(replica int32, instance int32, ballot int32, proposals []*genericsmr.Propose, cmds []state.Command, batchSize int) {
  //init command attributes

  seq := int32(0)
  var deps [DS]int32
  for q := 0; q < e.R.N; q++ {
    deps[q] = -1
  }
  if replica != e.R.Id {
    // fix (G32): a restarted phase 1 for another replica's instance depends on that replica's
    // earlier instances (updateAttributes skips row replica here and at every receiver, trusting
    // the instance's leader's own table)
    deps[replica] = instance - 1
  }

  seq, deps, _ = e.updateAttributes(cmds, seq, deps, replica, instance)
  base := gryffproto.ValTag{e.R.GetCurrentValue(cmds[0].K),
      *e.R.GetStoreMetadata(cmds[0].K).Tag}

  // fix (G9): the instance is (replica, instance): a recovering replica restarting phase 1 for
  // another replica's instance writes that instance (Leader = replica), records it in replica's
  // row of the conflict tables, and sends the PreAccepts for it (for a new proposal, replica is
  // this replica)
  e.InstanceSpace[replica][instance] = &Instance{
    cmds,
    ballot,
    epaxosproto.PREACCEPTED,
    seq,
    deps,
    base,
    &LeaderBookkeeping{proposals, 0, 0, true, 0, 0, 0, deps, []int32{-1, -1, -1, -1, -1}, nil, false, false, nil, 0, time.Time{},
      time.Time{}, time.Time{}, make([]time.Time, len(e.R.PeerAddrList)), 0, false},
    0, 0, nil, instance, replica,
    ballot} // fix (G16): the proposer's value, at its ballot

  e.updateConflicts(cmds, replica, instance, seq)

  if seq >= e.maxSeq {
    e.maxSeq = seq + 1
  }

  e.recordInstanceMetadata(e.InstanceSpace[replica][instance])
  e.recordCommands(cmds)
  e.sync()

  e.bcastPreAccept(replica, instance, ballot, cmds, seq, deps, base)

  cpcounter += batchSize

  if e.R.Id == 0 && DO_CHECKPOINTING && cpcounter >= CHECKPOINT_PERIOD {
    cpcounter = 0

    //Propose a checkpoint command to act like a barrier.
    //This allows replicas to discard their dependency hashtables.
    e.crtInstance[e.R.Id]++
    instance++

    e.maxSeq++
    for q := 0; q < e.R.N; q++ {
      deps[q] = e.crtInstance[q] - 1
    }

    e.InstanceSpace[e.R.Id][instance] = &Instance{
      cpMarker,
      0,
      epaxosproto.PREACCEPTED,
      e.maxSeq,
      deps,
      gryffproto.ValTag{0, gryffproto.Tag{0, 0, 0}},
      &LeaderBookkeeping{nil, 0, 0, true, 0, 0, 0, deps, nil, nil, false, false, nil, 0, time.Time{}, time.Time{}, time.Time{}, make([]time.Time, len(e.R.PeerAddrList)), 0, false},
      0,
      0,
      nil,
      instance, e.R.Id, 0}

    e.latestCPEPaxosRMWHandler = e.R.Id
    e.latestCPInstance = instance

    //discard dependency hashtables
    e.clearHashtables()

    e.recordInstanceMetadata(e.InstanceSpace[e.R.Id][instance])
    e.sync()

    e.bcastPreAccept(e.R.Id, instance, 0, cpMarker, e.maxSeq, deps, gryffproto.ValTag{0, gryffproto.Tag{0, 0, 0}})
  }
}

func (e *EPaxosRMWHandler) handlePreAccept(preAccept *gryffproto.PreAccept) {
  // fix (G10): the instance is (Replica, Instance), whoever sent the PreAccept (a recovering
  // replica sends it for another replica's instance); the reply goes to the sender (LeaderId)
  inst := e.InstanceSpace[preAccept.Replica][preAccept.Instance]

  if preAccept.Seq >= e.maxSeq {
    e.maxSeq = preAccept.Seq + 1
  }

  // fix (G23): an executed copy too (it stays executed)
  if inst != nil && (inst.Status == epaxosproto.COMMITTED || inst.Status == epaxosproto.ACCEPTED ||
      inst.Status == epaxosproto.EXECUTED) {
    //reordered handling of commit/accept and pre-accept
    // fix (G19): an accepted or committed copy is left as it is (an Accept and a Commit carry
    // the command; a late PreAccept fills nothing in)
    e.recordCommands(preAccept.Command)
    e.sync()
    return
  }

  if preAccept.Instance >= e.crtInstance[preAccept.Replica] {
    e.crtInstance[preAccept.Replica] = preAccept.Instance + 1
  }

  //update attributes for command
  seq, deps, _ := e.updateAttributes(preAccept.Command, preAccept.Seq, preAccept.Deps, preAccept.Replica, preAccept.Instance)
  // fix (G41): the copy is unchanged (PREACCEPTED_EQ) iff its attributes equal the PreAccept's
  // (updateAttributes reports a change whenever it raises seq, also when the int32 seq wraps back
  // to the PreAccept's own value)
  changed := seq != preAccept.Seq || !equal(&deps, &preAccept.Deps)
  base := preAccept.Base
  tag := *e.R.GetStoreMetadata(preAccept.Command[0].K).Tag 
  if tag.GreaterThan(base.T) {
    base.V = e.R.GetCurrentValue(preAccept.Command[0].K) 
    base.T = tag
    changed = true
  }

  uncommittedDeps := false
  for q := 0; q < e.R.N; q++ {
    if deps[q] > e.CommittedUpTo[q] {
      uncommittedDeps = true
      break
    }
  }
  status := epaxosproto.PREACCEPTED_EQ
  if changed {
    status = epaxosproto.PREACCEPTED
  }

  if inst != nil {
    if preAccept.Ballot < inst.ballot {
      e.replyPreAccept(preAccept.LeaderId,
        &gryffproto.PreAcceptReply{
          preAccept.Replica,
          preAccept.Instance,
          FALSE,
          inst.ballot,
          inst.Seq,
          inst.Deps,
          e.CommittedUpTo,
          inst.Base,
        })
      return
    } else {
      inst.Cmds = preAccept.Command
      inst.Seq = seq
      inst.Deps = deps
      inst.Base = base // fix (G20): the copy holds the base this replica replies with
      inst.ballot = preAccept.Ballot
      inst.vbal = preAccept.Ballot // fix (G16): the value pre-accepted at this ballot
      inst.Status = status
    }
  } else {
    e.InstanceSpace[preAccept.Replica][preAccept.Instance] = &Instance{
      preAccept.Command,
      preAccept.Ballot,
      status,
      seq,
      deps,
      base,
      nil, 0, 0,
      nil,
      preAccept.Instance,
      preAccept.Replica,
      preAccept.Ballot} // fix (G16): the value pre-accepted at this ballot
  }

  e.updateConflicts(preAccept.Command, preAccept.Replica, preAccept.Instance, preAccept.Seq)

  e.recordInstanceMetadata(e.InstanceSpace[preAccept.Replica][preAccept.Instance])
  e.recordCommands(preAccept.Command)
  e.sync()

  // fix (G36): an empty command is a checkpoint only when checkpointing is on (else it is a
  // no-op, and the conflict tables keep the instances they record)
  if DO_CHECKPOINTING && len(preAccept.Command) == 0 {
    //checkpoint
    //update latest checkpoint info
    e.latestCPEPaxosRMWHandler = preAccept.Replica
    e.latestCPInstance = preAccept.Instance

    //discard dependency hashtables
    e.clearHashtables()
  }

  if changed || uncommittedDeps || preAccept.Replica != preAccept.LeaderId || !isInitialBallot(preAccept.Ballot) {
    e.replyPreAccept(preAccept.LeaderId,
      &gryffproto.PreAcceptReply{
        preAccept.Replica,
        preAccept.Instance,
        TRUE,
        preAccept.Ballot,
        seq,
        deps,
        e.CommittedUpTo,
        base,
      })
  } else {
    pok := &epaxosproto.PreAcceptOK{preAccept.Instance}
    if e.broadcastOptimizationEnabled {
      e.R.SendMsg(preAccept.LeaderId, e.preAcceptOKRPC, pok)
      e.preAcceptOKs[preAccept.LeaderId][preAccept.Instance] += 2
      if e.preAcceptOKs[preAccept.LeaderId][preAccept.Instance] >= e.fastPathQuorum() {
        e.InstanceSpace[preAccept.LeaderId][preAccept.Instance].Status = epaxosproto.COMMITTED
        e.updateCommitted(preAccept.LeaderId)
      }
      e.bcastPreAcceptOKReply(preAccept.LeaderId, preAccept.Instance)
    } else{
      e.R.SendMsg(preAccept.LeaderId, e.preAcceptOKRPC, pok)
    }

  }
}

func (e *EPaxosRMWHandler) fastPathQuorum() int {
  F := e.R.N / 2
  if e.R.Thrifty {
    return F + (F + 1) / 2
  } else {
    return 2 * F
  }
}

func (e *EPaxosRMWHandler) handlePreAcceptReply(pareply *gryffproto.PreAcceptReply) {
  dlog.Printf("[%d.%d] Handling PreAcceptReply\n", pareply.Replica, pareply.Instance)
  inst := e.InstanceSpace[pareply.Replica][pareply.Instance]

  // we can't ignore the PreAccept reply if we've sent out Accept messages but are
  // still waiting for a fast path quorum. I guess the other way to implement this
  // is with a timeout after waiting for a fast path quorum
  // fix (G18): only while pre-accepted: once the Accept is sent (or the instance committed), the
  // ballot's value is fixed and a later reply changes nothing (one value per ballot)
  if inst.Status != epaxosproto.PREACCEPTED {
    // we've moved on, this is a delayed reply
    return
  }

  if inst.ballot != pareply.Ballot {
    return
  }

  if pareply.OK == FALSE {
    // TODO: there is probably another active leader
    inst.lb.nacks++
    if pareply.Ballot > inst.lb.maxRecvBallot {
      inst.lb.maxRecvBallot = pareply.Ballot
    }
    if inst.lb.nacks >= e.R.N/2 {
      // TODO
    }
    return
  }

  inst.lb.preAcceptOKs++

  var equal bool
  dlog.Printf("[%d.%d] before inst.Deps=%v, reply.Deps=%v.\n", pareply.Replica, pareply.Instance, inst.Deps, pareply.Deps)
  inst.Seq, inst.Deps, equal = e.mergeAttributes(inst.Seq, inst.Deps, pareply.Seq, pareply.Deps)
  if pareply.Base.T.GreaterThan(inst.Base.T) {
    gooseCopy7 := pareply.Base // verification workaround (T1): copy through a local
    inst.Base = gooseCopy7
    equal = false
  }
  dlog.Printf("[%d.%d] after inst.Deps=%v.\n", pareply.Replica, pareply.Instance, inst.Deps)
  if (e.R.N <= 3 && !e.R.Thrifty) || inst.lb.preAcceptOKs > 1 {
    inst.lb.allEqual = inst.lb.allEqual && equal
    if !equal {
      conflicted++
    }
  }

  allCommitted := true
  if e.R.N > 3 {
    // we only need optimized egalitarian paxos for more than 3 replicas
    // with 3 replicas, the fast path quorum for simple EPaxos is the same as for optimized EPaxos
    for q := 0; q < e.R.N; q++ {
      if inst.lb.committedDeps[q] < pareply.CommittedDeps[q] {
        inst.lb.committedDeps[q] = pareply.CommittedDeps[q]
      }
      if inst.lb.committedDeps[q] < e.CommittedUpTo[q] {
        inst.lb.committedDeps[q] = e.CommittedUpTo[q]
      }
      if inst.lb.committedDeps[q] < inst.Deps[q] {
        dlog.Printf("[%d.%d] comittedDeps=%v, reply.committedDeps=%v. comittedUpTo=%v, inst.Deps=%v.\n", pareply.Replica, pareply.Instance,
          inst.lb.committedDeps, pareply.CommittedDeps, e.CommittedUpTo, inst.Deps)
        dlog.Printf("[%d.%d] Have not committed all deps from replica %d (%d, %d).\n", pareply.Replica, pareply.Instance, q,
          inst.lb.committedDeps[q], inst.Deps[q])
        allCommitted = false
      }
    }
  }

  dlog.Printf("[%d.%d] PreAcceptOKs: %d (%d total replicas).\n", pareply.Replica, pareply.Instance,
    inst.lb.preAcceptOKs, e.R.N)
  //can we commit on the fast path?
  // fastPathQuorum-1 because leader is in quorum
  if inst.lb.preAcceptOKs >= e.fastPathQuorum()-1 && inst.lb.allEqual && allCommitted && isInitialBallot(inst.ballot) {
    happy++
    dlog.Printf("Fast path for instance %d.%d\n", pareply.Replica, pareply.Instance)
    inst.lb.committedTime = time.Now()
    e.InstanceSpace[pareply.Replica][pareply.Instance].Status = epaxosproto.COMMITTED
    e.updateCommitted(pareply.Replica)
    writeKey0 := false
    readKey0 := false
    if inst.lb.clientProposals != nil && len(inst.Cmds) < len(inst.lb.clientProposals) {
      // fix (G11): the committed value is not the clients' (a recovery chose another, e.g. a
      // no-op): propose them again, as handleCommit does, and drop the bookkeeping
      for _, p := range inst.lb.clientProposals {
        e.R.ProposeChan <- p
      }
      inst.lb = nil
    } else if inst.lb.clientProposals != nil {
      // give clients the all clear
      for i := 0; i < len(inst.lb.clientProposals); i++ {
        if inst.Cmds[i].K == 0 {
          if inst.Cmds[i].Op == state.PUT {
            writeKey0 = true
          } else if inst.Cmds[i].Op == state.GET {
            readKey0 = true
          }
        }
        if !e.R.NeedsWaitForExecute(&inst.Cmds[i]) {
          dlog.Printf("[%d.%d.%d] Replying to request %d before execute %d.\n", pareply.Replica, pareply.Instance, i,
            inst.lb.clientProposals[i].CommandId, inst.Cmds[i].Op)
          e.R.ReplyProposeTS(
            &genericsmrproto.ProposeReplyTS{
              TRUE,
              inst.lb.clientProposals[i].CommandId,
              state.NIL,
              inst.lb.clientProposals[i].Timestamp},
            inst.lb.clientProposals[i].Reply)
        }
      }
    }

    e.recordInstanceMetadata(inst)
    e.sync() //is this necessary here?

    e.R.Stats.Increment("fast_path")
    if writeKey0 {
      e.R.Stats.Increment("fast_writes_0")
    } else if readKey0 {
      e.R.Stats.Increment("fast_reads_0")
    }

    dlog.Printf("[%d.%d] Committing on fast path.\n", pareply.Replica, pareply.Instance)
    dlog.Printf("[%d.%d] Need wait for deps=%v before execute.\n", pareply.Replica, pareply.Instance, inst.Deps)
    e.bcastCommit(pareply.Replica, pareply.Instance, inst.Cmds, inst.Seq, inst.Deps, inst.Base)
  } else if inst.lb.preAcceptOKs >= e.R.N/2 {
    if !allCommitted {
      weird++
    }
    slow++
    inst.Status = epaxosproto.ACCEPTED
    inst.vbal = inst.ballot // fix (G16): the proposer accepts its own value at its ballot
    dlog.Printf("[%d.%d] Slow because allEqual=%v, allCommitted=%v, isInitialBallot=%v,preAcceptOKs=%d,fpq=%d.\n", pareply.Replica,
      pareply.Instance, inst.lb.allEqual, allCommitted, isInitialBallot(inst.ballot), inst.lb.preAcceptOKs, e.fastPathQuorum())
    e.bcastAccept(pareply.Replica, pareply.Instance, inst.ballot, inst.Cmds, inst.Seq, inst.Deps, inst.Base)
  }
  //TODO: take the slow path if messages are slow to arrive
}

func (e *EPaxosRMWHandler) handlePreAcceptOKReply(paok *gryffproto.PreAcceptOKReply) {
  if paok.Replica == e.R.Id {
    // paokreply is redundant with paok or pareply
    return
  }

  e.preAcceptOKs[paok.Replica][paok.Instance]++
  inst := e.InstanceSpace[paok.Replica][paok.Instance]

  if inst != nil && e.preAcceptOKs[paok.Replica][paok.Instance] >= e.fastPathQuorum() {
    inst.Status = epaxosproto.COMMITTED
    e.updateCommitted(paok.Replica)
  }
}

func (e *EPaxosRMWHandler) handleAcceptOKReply(aok *gryffproto.AcceptOKReply) {
  if aok.Replica == e.R.Id {
    // paokreply is redundant with paok or pareply
    return
  }

  e.acceptOKs[aok.Replica][aok.Instance]++
  inst := e.InstanceSpace[aok.Replica][aok.Instance]

  if inst != nil && e.acceptOKs[aok.Replica][aok.Instance] >= e.R.N/2 {
    inst.Status = epaxosproto.COMMITTED
    e.updateCommitted(aok.Replica)
  }
}

func (e *EPaxosRMWHandler) handlePreAcceptOK(pareply *epaxosproto.PreAcceptOK) {
  dlog.Printf("[%d.%d] Handling PreAcceptOK\n", e.R.Id, pareply.Instance)
  inst := e.InstanceSpace[e.R.Id][pareply.Instance]

  // we can't ignore the PreAccept reply if we've sent out Accept messages but are
  // still waiting for a fast path quorum. I guess the other way to implement this
  // is with a timeout after waiting for a fast path quorum
  // fix (G18): only while pre-accepted (one value per ballot), as handlePreAcceptReply
  if inst.Status != epaxosproto.PREACCEPTED {
    // we've moved on, this is a delayed reply
    return
  }

  if !isInitialBallot(inst.ballot) {
    return
  }

  inst.lb.preAcceptOKs++

  allCommitted := true
  if e.R.N > 3 {
    // we only need optimized egalitarian paxos for more than 3 replicas
    // with 3 replicas, the fast path quorum for simple EPaxos is the same as for optimized EPaxos
    for q := 0; q < e.R.N; q++ {
      if inst.lb.committedDeps[q] < inst.lb.originalDeps[q] {
        inst.lb.committedDeps[q] = inst.lb.originalDeps[q]
      }
      if inst.lb.committedDeps[q] < e.CommittedUpTo[q] {
        inst.lb.committedDeps[q] = e.CommittedUpTo[q]
      }
      if inst.lb.committedDeps[q] < inst.Deps[q] {
        dlog.Printf("[%d.%d] comittedDeps=%v, originalDeps=%v. comittedUpTo=%v, inst.Deps=%v.\n", e.R.Id, pareply.Instance,
          inst.lb.committedDeps, inst.lb.originalDeps, e.CommittedUpTo, inst.Deps)
        dlog.Printf("[%d.%d] Have not committed all deps from replica %d (%d, %d).\n", e.R.Id, pareply.Instance, q,
          inst.lb.committedDeps[q], inst.Deps[q])

        allCommitted = false
      }
    }
  }

  dlog.Printf("[%d.%d] PreAcceptOKs: %d (%d total replicas).\n", e.R.Id, pareply.Instance,
    inst.lb.preAcceptOKs, e.R.N)
  //can we commit on the fast path?
  if inst.lb.preAcceptOKs >= e.fastPathQuorum()-1 && inst.lb.allEqual && allCommitted && isInitialBallot(inst.ballot) {
    happy++
    e.InstanceSpace[e.R.Id][pareply.Instance].Status = epaxosproto.COMMITTED
    e.updateCommitted(e.R.Id)
    inst.lb.committedTime = time.Now()
    writeKey0 := false
    readKey0 := false
    if inst.lb.clientProposals != nil && len(inst.Cmds) < len(inst.lb.clientProposals) {
      // fix (G11): the committed value is not the clients' (a recovery chose another, e.g. a
      // no-op): propose them again, as handleCommit does, and drop the bookkeeping
      for _, p := range inst.lb.clientProposals {
        e.R.ProposeChan <- p
      }
      inst.lb = nil
    } else if inst.lb.clientProposals != nil {
      // give clients the all clear
      for i := 0; i < len(inst.lb.clientProposals); i++ {
        if inst.Cmds[i].K == 0 {
          if inst.Cmds[i].Op == state.PUT {
            writeKey0 = true
          } else if inst.Cmds[i].Op == state.GET {
            readKey0 = true
          }
        }
        if !e.R.NeedsWaitForExecute(&inst.Cmds[i]) {
          dlog.Printf("[%d.%d.%d] Replying to client before execute.\n", e.R.Id, pareply.Instance, i, inst.Cmds[i].Op)
          e.R.ReplyProposeTS(
            &genericsmrproto.ProposeReplyTS{
              TRUE,
              inst.lb.clientProposals[i].CommandId,
              state.NIL,
              inst.lb.clientProposals[i].Timestamp},
            inst.lb.clientProposals[i].Reply)
        }
      }
    }

    e.recordInstanceMetadata(inst)
    e.sync() //is this necessary here?
    e.R.Stats.Increment("fast_path")
    if writeKey0 {
      e.R.Stats.Increment("fast_writes_0")
    } else if readKey0 {
      e.R.Stats.Increment("fast_reads_0")
    }

    dlog.Printf("[%d.%d] Committing on fast path.\n", e.R.Id, pareply.Instance)
    dlog.Printf("[%d.%d] Need wait for deps=%v before execute.\n", e.R.Id, pareply.Instance, inst.Deps)
    e.bcastCommit(e.R.Id, pareply.Instance, inst.Cmds, inst.Seq, inst.Deps, inst.Base)
  } else if inst.lb.preAcceptOKs >= e.R.N/2 {
    if !allCommitted {
      weird++
    }
    slow++
    inst.Status = epaxosproto.ACCEPTED
    inst.vbal = inst.ballot // fix (G16): the proposer accepts its own value at its ballot
    dlog.Printf("[%d.%d] Slow because allEqual=%v, allCommitted=%v, isInitialBallot=%v,preAcceptOKs=%d,fpq=%d.\n", e.R.Id,
      pareply.Instance, inst.lb.allEqual, allCommitted, isInitialBallot(inst.ballot), inst.lb.preAcceptOKs, e.fastPathQuorum())
    e.bcastAccept(e.R.Id, pareply.Instance, inst.ballot, inst.Cmds, inst.Seq, inst.Deps, inst.Base)
  }
  //TODO: take the slow path if messages are slow to arrive
}

/**********************************************************************

                        PHASE 2

***********************************************************************/

func (e *EPaxosRMWHandler) handleAccept(accept *gryffproto.EAccept) {
  // fix (G10): the instance is (Replica, Instance), whoever sent the Accept (a recovering replica
  // sends it for another replica's instance); the reply goes to the sender (LeaderId)
  inst := e.InstanceSpace[accept.Replica][accept.Instance]

  if accept.Seq >= e.maxSeq {
    e.maxSeq = accept.Seq + 1
  }

  if inst != nil && (inst.Status == epaxosproto.COMMITTED || inst.Status == epaxosproto.EXECUTED) {
    return
  }

  if accept.Instance >= e.crtInstance[accept.Replica] { // fix (G10)
    e.crtInstance[accept.Replica] = accept.Instance + 1
  }

  if inst != nil {
    if accept.Ballot < inst.ballot {
      e.replyAccept(accept.LeaderId, &epaxosproto.AcceptReply{accept.Replica, accept.Instance, FALSE, inst.ballot})
      return
    }
    inst.Status = epaxosproto.ACCEPTED
    // fix (G15, G16): accepting at a ballot promises it, and the value is adopted at it
    inst.ballot = accept.Ballot
    inst.vbal = accept.Ballot
    inst.Cmds = accept.Command // fix (G19): the accepted command, as its attributes
    inst.Seq = accept.Seq
    gooseCopy16 := accept.Deps // verification workaround (T1): copy through a local
    inst.Deps = gooseCopy16
    gooseCopy6 := accept.Base // verification workaround (T1): copy through a local
    inst.Base = gooseCopy6
  } else {
    e.InstanceSpace[accept.Replica][accept.Instance] = &Instance{ // fix (G10): row Replica, Leader Replica
      accept.Command, // fix (G19): the accepted command
      accept.Ballot,
      epaxosproto.ACCEPTED,
      accept.Seq,
      accept.Deps,
      accept.Base,
      nil, 0, 0, nil, accept.Instance, accept.Replica,
      accept.Ballot} // fix (G16): the value accepted at this ballot

    // fix (G36): an empty command is a checkpoint only when checkpointing is on (else it is a
    // no-op, and the conflict tables keep the instances they record)
    if DO_CHECKPOINTING && accept.Count == 0 {
      //checkpoint
      //update latest checkpoint info
      e.latestCPEPaxosRMWHandler = accept.Replica
      e.latestCPInstance = accept.Instance

      //discard dependency hashtables
      e.clearHashtables()
    }
  }

  e.recordInstanceMetadata(e.InstanceSpace[accept.Replica][accept.Instance])
  e.sync()

  e.replyAccept(accept.LeaderId,
    &epaxosproto.AcceptReply{
      accept.Replica,
      accept.Instance,
      TRUE,
      accept.Ballot})
  
  if e.broadcastOptimizationEnabled {
    e.acceptOKs[accept.Replica][accept.Instance] += 2
    if e.acceptOKs[accept.Replica][accept.Instance] >= e.R.N/2 {
        e.InstanceSpace[accept.Replica][accept.Instance].Status = epaxosproto.COMMITTED
        e.updateCommitted(accept.Replica)
      }

    e.bcastAcceptOKReply(accept.Replica, accept.Instance)
  }
}

func (e *EPaxosRMWHandler) handleAcceptReply(areply *epaxosproto.AcceptReply) {
  inst := e.InstanceSpace[areply.Replica][areply.Instance]

  if inst.Status != epaxosproto.ACCEPTED {
    // we've move on, these are delayed replies, so just ignore
    return
  }

  if inst.ballot != areply.Ballot {
    return
  }

  if areply.OK == FALSE {
    // TODO: there is probably another active leader
    inst.lb.nacks++
    if areply.Ballot > inst.lb.maxRecvBallot {
      inst.lb.maxRecvBallot = areply.Ballot
    }
    if inst.lb.nacks >= e.R.N/2 {
      // TODO
    }
    return
  }

  inst.lb.acceptOKs++

  if inst.lb.acceptOKs+1 > e.R.N/2 {
    inst.lb.committedTime = time.Now()
    e.InstanceSpace[areply.Replica][areply.Instance].Status = epaxosproto.COMMITTED
    e.updateCommitted(areply.Replica)
    writeKey0 := false
    readKey0 := false
    if inst.lb.clientProposals != nil && len(inst.Cmds) < len(inst.lb.clientProposals) {
      // fix (G11): the committed value is not the clients' (a recovery chose another, e.g. a
      // no-op): propose them again, as handleCommit does, and drop the bookkeeping
      for _, p := range inst.lb.clientProposals {
        e.R.ProposeChan <- p
      }
      inst.lb = nil
    } else if inst.lb.clientProposals != nil {
      // give clients the all clear
      for i := 0; i < len(inst.lb.clientProposals); i++ {
        if inst.Cmds[i].K == 0 {
          if inst.Cmds[i].Op == state.PUT {
            writeKey0 = true
          } else if inst.Cmds[i].Op == state.GET {
            readKey0 = true
          }
        }
        if !e.R.NeedsWaitForExecute(&inst.Cmds[i]) {
          dlog.Printf("[%d.%d.%d] Replying to client before execute %d.\n", e.R.Id, areply.Instance, i, inst.Cmds[i].Op)
          e.R.ReplyProposeTS(
            &genericsmrproto.ProposeReplyTS{
              TRUE,
              inst.lb.clientProposals[i].CommandId,
              state.NIL,
              inst.lb.clientProposals[i].Timestamp},
            inst.lb.clientProposals[i].Reply)
        }
      }
    }

    e.recordInstanceMetadata(inst)
    e.sync() //is this necessary here?
    e.R.Stats.Increment("slow_path")
    if writeKey0 {
      e.R.Stats.Increment("slow_writes_0")
    } else if readKey0 {
      e.R.Stats.Increment("slow_reads_0")
    }

    dlog.Printf("[%d.%d] Committing on slow path.\n", areply.Replica, areply.Instance)
    e.bcastCommit(areply.Replica, areply.Instance, inst.Cmds, inst.Seq, inst.Deps, inst.Base)
  }
}

/**********************************************************************

                            COMMIT

***********************************************************************/

func (e *EPaxosRMWHandler) handleCommit(commit *gryffproto.ECommit) {
  dlog.Printf("[%d.%d] Received Commit.\n", commit.Replica, commit.Instance)
  inst := e.InstanceSpace[commit.Replica][commit.Instance]

  if commit.Seq >= e.maxSeq {
    e.maxSeq = commit.Seq + 1
  }

  if commit.Instance >= e.crtInstance[commit.Replica] {
    e.crtInstance[commit.Replica] = commit.Instance + 1
  }

  if inst != nil && inst.Status == epaxosproto.EXECUTED {
    // fix (G23): an executed copy stays executed (a late Commit carries the same value)
    return
  }

  if inst != nil {
    if inst.lb != nil && inst.lb.clientProposals != nil && len(commit.Command) == 0 {
      //someone committed a NO-OP, but we have proposals for this instance
      //try in a different instance
      for _, p := range inst.lb.clientProposals {
        e.R.ProposeChan <- p
      }
      inst.lb = nil
    }
    // in case we need to execute commands
    inst.Cmds = commit.Command
    inst.Seq = commit.Seq
    gooseCopy5 := commit.Deps // verification workaround (T1): copy through a local
    inst.Deps = gooseCopy5
    // fix (G3): the committed base, as the commit's other attributes (every replica executes
    // the command from the base its leader committed)
    commitBase := commit.Base
    inst.Base = commitBase
    inst.Status = epaxosproto.COMMITTED
  } else {
    dlog.Printf("[%d.%d] Updated with committed instance.\n", commit.Replica, commit.Instance)
    e.InstanceSpace[commit.Replica][int(commit.Instance)] = &Instance{
      commit.Command,
      0,
      epaxosproto.COMMITTED,
      commit.Seq,
      commit.Deps,
      commit.Base,
      nil,
      0,
      0,
      nil,
      commit.Instance,
      commit.Replica, 0}

    e.updateConflicts(commit.Command, commit.Replica, commit.Instance, commit.Seq)

    // fix (G36): an empty command is a checkpoint only when checkpointing is on (else it is a
    // no-op, and the conflict tables keep the instances they record)
    if DO_CHECKPOINTING && len(commit.Command) == 0 {
      //checkpoint
      //update latest checkpoint info
      e.latestCPEPaxosRMWHandler = commit.Replica
      e.latestCPInstance = commit.Instance

      //discard dependency hashtables
      e.clearHashtables()
    }
  }
  e.updateCommitted(commit.Replica)

  e.recordInstanceMetadata(e.InstanceSpace[commit.Replica][commit.Instance])
  e.recordCommands(commit.Command)
}

func (e *EPaxosRMWHandler) handleCommitShort(commit *epaxosproto.CommitShort) {
  inst := e.InstanceSpace[commit.Replica][commit.Instance]

  if commit.Instance >= e.crtInstance[commit.Replica] {
    e.crtInstance[commit.Replica] = commit.Instance + 1
  }

  if inst != nil {
    if inst.lb != nil && inst.lb.clientProposals != nil {
      //try command in a different instance
      for _, p := range inst.lb.clientProposals {
        e.R.ProposeChan <- p
      }
      inst.lb = nil
    }
    inst.Seq = commit.Seq
    gooseCopy4 := commit.Deps // verification workaround (T1): copy through a local
    inst.Deps = gooseCopy4
    inst.Status = epaxosproto.COMMITTED
  } else {
    e.InstanceSpace[commit.Replica][commit.Instance] = &Instance{
      nil,
      0,
      epaxosproto.COMMITTED,
      commit.Seq,
      commit.Deps,
      gryffproto.ValTag{0, gryffproto.Tag{0, 0, 0}},
      nil, 0, 0, nil, commit.Instance, commit.Replica, 0}

    if commit.Count == 0 {
      //checkpoint
      //update latest checkpoint info
      e.latestCPEPaxosRMWHandler = commit.Replica
      e.latestCPInstance = commit.Instance

      //discard dependency hashtables
      e.clearHashtables()
    }
  }
  e.updateCommitted(commit.Replica)

  e.recordInstanceMetadata(e.InstanceSpace[commit.Replica][commit.Instance])
}

/**********************************************************************

                      RECOVERY ACTIONS

***********************************************************************/

func (e *EPaxosRMWHandler) startRecoveryForInstance(replica int32, instance int32) {
  var nildeps [DS]int32

  if c := e.InstanceSpace[replica][instance]; c != nil &&
      (c.Status == epaxosproto.COMMITTED || c.Status == epaxosproto.EXECUTED) {
    // fix (G21): committed here (the executor's request was late): nothing to recover
    return
  }
  if c := e.InstanceSpace[replica][instance]; c != nil && (c.ballot >> 4) >= (math.MaxInt32 >> 4) {
    // fix (G39): no larger ballot exists (makeBallotLargerThan would wrap negative, lowering
    // the promise): recovery does not start
    return
  }

  if e.InstanceSpace[replica][instance] == nil {
    e.InstanceSpace[replica][instance] = &Instance{nil, 0, epaxosproto.NONE, 0, nildeps, gryffproto.ValTag{0, gryffproto.Tag{0, 0, 0}}, nil, 0, 0, nil, instance, replica, -1}
  }

  inst := e.InstanceSpace[replica][instance]
  if inst.lb == nil {
    inst.lb = &LeaderBookkeeping{nil, -1, 0, false, 0, 0, 0, nildeps, nil, nil, true, false, nil, 0, time.Time{}, time.Time{},
      time.Time{}, make([]time.Time, len(e.R.PeerAddrList)), 0, false}

  } else {
    inst.lb = &LeaderBookkeeping{inst.lb.clientProposals, -1, 0, false, 0, 0, 0, nildeps, nil, nil, true, false, nil, 0,
      time.Time{}, time.Time{}, time.Time{}, make([]time.Time, len(e.R.PeerAddrList)), 0, false}
  }

  // fix (G16, G42): the candidate records the ballot at which the copy adopted its value (vbal),
  // not the copy's promise
  if inst.Status == epaxosproto.ACCEPTED {
    inst.lb.recoveryInst = &RecoveryInstance{inst.Cmds, inst.Status, inst.Seq, inst.Deps, inst.Base, 0, false, inst.vbal}
  } else if inst.Status >= epaxosproto.PREACCEPTED {
    // fix (G24): the own copy counts toward the candidate only if it is unchanged from the
    // leader's initial PreAccept (PREACCEPTED_EQ at ballot 0, at a replica other than the leader)
    count := 0
    if inst.Status == epaxosproto.PREACCEPTED_EQ && inst.vbal == 0 && e.R.Id != replica {
      count = 1
    }
    inst.lb.recoveryInst = &RecoveryInstance{inst.Cmds, inst.Status, inst.Seq, inst.Deps, inst.Base, count, (e.R.Id == replica), inst.vbal}
  }

  //compute larger ballot
  inst.ballot = e.makeBallotLargerThan(inst.ballot)

  e.bcastPrepare(replica, instance, inst.ballot)
}

func (e *EPaxosRMWHandler) handlePrepare(prepare *epaxosproto.Prepare) {
  inst := e.InstanceSpace[prepare.Replica][prepare.Instance]
  var preply *gryffproto.PrepareReply
  var nildeps [DS]int32

  if inst == nil {
    e.InstanceSpace[prepare.Replica][prepare.Instance] = &Instance{
      nil,
      prepare.Ballot,
      epaxosproto.NONE,
      0,
      nildeps,
      gryffproto.ValTag{0, gryffproto.Tag{0, 0, 0}},
      nil, 0, 0, nil, prepare.Instance, prepare.Replica, -1}
    preply = &gryffproto.PrepareReply{
      e.R.Id,
      prepare.Replica,
      prepare.Instance,
      TRUE,
      prepare.Ballot, // fix (G17): the new copy's promise (the Prepare's ballot)
      -1, // fix (G16): no value adopted
      epaxosproto.NONE,
      nil,
      -1,
      nildeps,
      gryffproto.ValTag{0, gryffproto.Tag{0, 0, 0}}}
  } else {
    ok := TRUE
    if prepare.Ballot < inst.ballot {
      ok = FALSE
    } else {
      inst.ballot = prepare.Ballot
    }
    preply = &gryffproto.PrepareReply{
      e.R.Id,
      prepare.Replica,
      prepare.Instance,
      ok,
      inst.ballot,
      inst.vbal, // fix (G16): the ballot at which the copy adopted its value
      inst.Status,
      inst.Cmds,
      inst.Seq,
      inst.Deps,
      inst.Base}
  }

  e.replyPrepare(prepare.LeaderId, preply)
}

func (e *EPaxosRMWHandler) handlePrepareReply(preply *gryffproto.PrepareReply) {
  inst := e.InstanceSpace[preply.Replica][preply.Instance]

  if inst.lb == nil || !inst.lb.preparing {
    // we've moved on -- these are delayed replies, so just ignore
    // TODO: should replies for non-current ballots be ignored?
    return
  }

  if inst.Status == epaxosproto.COMMITTED || inst.Status == epaxosproto.EXECUTED {
    // fix (G21): the instance committed here during the recovery: its attributes are final
    return
  }

  if preply.OK == FALSE {
    // TODO: there is probably another active leader, back off and retry later
    inst.lb.nacks++
    return
  }

  if preply.Ballot != inst.ballot {
    // fix (G17): a promise for another ballot (an earlier recovery of this instance) does not
    // count for this one
    return
  }

  //Got an ACK (preply.OK == TRUE)

  inst.lb.prepareOKs++

  if preply.Status == epaxosproto.COMMITTED || preply.Status == epaxosproto.EXECUTED {
    e.InstanceSpace[preply.Replica][preply.Instance] = &Instance{
      preply.Command,
      inst.ballot,
      epaxosproto.COMMITTED,
      preply.Seq,
      preply.Deps,
      preply.Base,
      nil, 0, 0, nil, preply.Instance, preply.Replica, inst.ballot}
    // fix (G22): the committed command (the reply's), not this replica's old copy's
    e.bcastCommit(preply.Replica, preply.Instance, preply.Command, preply.Seq, preply.Deps, preply.Base)
    //TODO: check if we should send notifications to clients
    return
  }

  if preply.Status == epaxosproto.ACCEPTED {
    // fix (G16, G42): the accepted copy of the greatest vbal wins (the reply's Ballot is its
    // promise, just raised to this recovery's ballot)
    if inst.lb.recoveryInst == nil || inst.lb.recoveryInst.status != epaxosproto.ACCEPTED ||
        inst.lb.recoveryInst.vbal < preply.VBallot {
      inst.lb.recoveryInst = &RecoveryInstance{preply.Command, preply.Status, preply.Seq, preply.Deps, preply.Base, 0, false, preply.VBallot}
    }
  }

  if (preply.Status == epaxosproto.PREACCEPTED || preply.Status == epaxosproto.PREACCEPTED_EQ) &&
    (inst.lb.recoveryInst == nil || inst.lb.recoveryInst.status < epaxosproto.ACCEPTED) {
    // fix (G24): only a copy unchanged from the leader's initial PreAccept (PREACCEPTED_EQ at
    // ballot 0, from a replica other than the leader: attributes and base as the leader proposed
    // them, so all such copies are equal) counts toward the candidate (preAcceptCount); such a
    // copy replaces a candidate that is not one, keeping whether the leader responded
    unchanged := preply.Status == epaxosproto.PREACCEPTED_EQ && preply.VBallot == 0 &&
      preply.AcceptorId != preply.Replica
    count := 0
    if unchanged {
      count = 1
    }
    if inst.lb.recoveryInst == nil {
      inst.lb.recoveryInst = &RecoveryInstance{preply.Command, preply.Status, preply.Seq, preply.Deps, preply.Base, count, false, preply.VBallot}
    } else if unchanged && inst.lb.recoveryInst.preAcceptCount > 0 {
      inst.lb.recoveryInst.preAcceptCount++
    } else if unchanged {
      // If we get different ordering attributes from pre-acceptors, we must go with the ones
      // that agreed with the initial command leader (in case we do not use Thrifty).
      // This is safe if we use thrifty, although we can also safely start phase 1 in that case.
      inst.lb.recoveryInst = &RecoveryInstance{preply.Command, preply.Status, preply.Seq, preply.Deps, preply.Base, 1, inst.lb.recoveryInst.leaderResponded, preply.VBallot}
    }
    if preply.AcceptorId == preply.Replica {
      //if the reply is from the initial command leader, then it's safe to restart phase 1
      inst.lb.recoveryInst.leaderResponded = true
      return
    }
  }

  if inst.lb.prepareOKs < e.R.N/2 {
    return
  }

  //Received Prepare replies from a majority

  ir := inst.lb.recoveryInst

  if ir != nil {
    //at least one replica has (pre-)accepted this instance
    if ir.status == epaxosproto.ACCEPTED ||
      (!ir.leaderResponded && ir.preAcceptCount >= e.R.N/2 && (e.R.Thrifty || ir.status == epaxosproto.PREACCEPTED_EQ)) {
      //safe to go to Accept phase
      inst.Cmds = ir.cmds
      inst.Seq = ir.seq
      gooseCopy20 := ir.deps // verification workaround (T1): copy through a local
      inst.Deps = gooseCopy20
      gooseCopy19 := ir.base // verification workaround (T1): copy through a local
      inst.Base = gooseCopy19
      inst.Status = epaxosproto.ACCEPTED
      inst.vbal = inst.ballot // fix (G16): the recovering replica accepts the value at its ballot
      inst.lb.preparing = false
      e.bcastAccept(preply.Replica, preply.Instance, inst.ballot, inst.Cmds, inst.Seq, inst.Deps, inst.Base)
    } else if !ir.leaderResponded && ir.preAcceptCount >= (e.R.N/2+1)/2 {
      //send TryPreAccepts
      //but first try to pre-accept on the local replica
      inst.lb.preAcceptOKs = 0
      inst.lb.nacks = 0
      inst.lb.possibleQuorum = make([]bool, e.R.N)
      for q := 0; q < e.R.N; q++ {
        inst.lb.possibleQuorum[q] = true
      }
      if conf, q, i := e.findPreAcceptConflicts(ir.cmds, preply.Replica, preply.Instance, ir.seq, ir.deps); conf {
        if e.InstanceSpace[q][i].Status >= epaxosproto.COMMITTED {
          //start Phase1 in the initial leader's instance
          e.startPhase1(preply.Replica, preply.Instance, inst.ballot, inst.lb.clientProposals, ir.cmds, len(ir.cmds))
          return
        } else {
          inst.lb.nacks = 1
          inst.lb.possibleQuorum[e.R.Id] = false
        }
      } else {
        inst.Cmds = ir.cmds
        inst.Seq = ir.seq
        gooseCopy15 := ir.deps // verification workaround (T1): copy through a local
        inst.Deps = gooseCopy15
        gooseCopy3 := ir.base // verification workaround (T1): copy through a local
        inst.Base = gooseCopy3
        inst.Status = epaxosproto.PREACCEPTED
        inst.vbal = inst.ballot // fix (G16): pre-accepted at this ballot
        inst.lb.preAcceptOKs = 1
      }
      inst.lb.preparing = false
      inst.lb.tryingToPreAccept = true
      e.bcastTryPreAccept(preply.Replica, preply.Instance, inst.ballot, inst.Cmds, inst.Seq, inst.Deps, inst.Base)
    } else {
      //start Phase1 in the initial leader's instance
      inst.lb.preparing = false
      e.startPhase1(preply.Replica, preply.Instance, inst.ballot, inst.lb.clientProposals, ir.cmds, len(ir.cmds))
    }
  } else {
    //try to finalize instance by proposing NO-OP
    var noop_deps [DS]int32
    // commands that depended on this instance must look at all previous instances
    noop_deps[preply.Replica] = preply.Instance - 1
    inst.lb.preparing = false
    e.InstanceSpace[preply.Replica][preply.Instance] = &Instance{
      []state.Command{}, // fix (G44): a no-op has no command (as a Commit delivers it), not an unknown one (nil)
      inst.ballot,
      epaxosproto.ACCEPTED,
      0,
      noop_deps,
      gryffproto.ValTag{0, gryffproto.Tag{0, 0, 0}},
      inst.lb, 0, 0, nil, preply.Instance, preply.Replica,
      inst.ballot} // fix (G16): the recovering replica accepts the no-op at its ballot
    e.bcastAccept(preply.Replica, preply.Instance, inst.ballot, nil, 0, noop_deps,gryffproto.ValTag{0, gryffproto.Tag{0, 0, 0,}})
  }
}

func (e *EPaxosRMWHandler) handleTryPreAccept(tpa *gryffproto.TryPreAccept) {
  inst := e.InstanceSpace[tpa.Replica][tpa.Instance]
  if inst != nil && inst.ballot > tpa.Ballot {
    // ballot number too small
    e.replyTryPreAccept(tpa.LeaderId, &epaxosproto.TryPreAcceptReply{
      e.R.Id,
      tpa.Replica,
      tpa.Instance,
      FALSE,
      inst.ballot,
      tpa.Replica,
      tpa.Instance,
      inst.Status})
  }
  
  changed := false
  base := tpa.Base
  tag := *e.R.GetStoreMetadata(tpa.Command[0].K).Tag 
  if tag.GreaterThan(base.T) {
    base.V = e.R.GetCurrentValue(tpa.Command[0].K) 
    base.T = tag
    changed = true
  }

  if conflict, confRep, confInst := e.findPreAcceptConflicts(tpa.Command, tpa.Replica, tpa.Instance, tpa.Seq, tpa.Deps); conflict || changed {
    // there is a conflict, can't pre-accept
    e.replyTryPreAccept(tpa.LeaderId, &epaxosproto.TryPreAcceptReply{
      e.R.Id,
      tpa.Replica,
      tpa.Instance,
      FALSE,
      inst.ballot,
      confRep,
      confInst,
      e.InstanceSpace[confRep][confInst].Status})
  } else {
    // can pre-accept
    if tpa.Instance >= e.crtInstance[tpa.Replica] {
      e.crtInstance[tpa.Replica] = tpa.Instance + 1
    }
    if inst != nil {
      inst.Cmds = tpa.Command
      gooseCopy14 := tpa.Deps // verification workaround (T1): copy through a local
      inst.Deps = gooseCopy14
      inst.Seq = tpa.Seq
      gooseCopy2 := tpa.Base // verification workaround (T1): copy through a local
      inst.Base = gooseCopy2
      inst.Status = epaxosproto.PREACCEPTED
      inst.ballot = tpa.Ballot
      inst.vbal = tpa.Ballot // fix (G16): pre-accepted at this ballot
    } else {
      e.InstanceSpace[tpa.Replica][tpa.Instance] = &Instance{
        tpa.Command,
        tpa.Ballot,
        epaxosproto.PREACCEPTED,
        tpa.Seq,
        tpa.Deps,
        tpa.Base,
        nil, 0, 0,
        nil,
        tpa.Instance, tpa.Replica, tpa.Ballot}
    }
    e.replyTryPreAccept(tpa.LeaderId, &epaxosproto.TryPreAcceptReply{e.R.Id, tpa.Replica, tpa.Instance, TRUE, inst.ballot, 0, 0, 0})
  }
}

func (e *EPaxosRMWHandler) findPreAcceptConflicts(cmds []state.Command, replica int32, instance int32, seq int32, deps [DS]int32) (bool, int32, int32) {
  inst := e.InstanceSpace[replica][instance]
  if inst != nil && len(inst.Cmds) > 0 {
    if inst.Status >= epaxosproto.ACCEPTED {
      // already ACCEPTED or COMMITTED
      // we consider this a conflict because we shouldn't regress to PRE-ACCEPTED
      return true, replica, instance
    }
    if inst.Seq == tpa.Seq && equal(&inst.Deps, &tpa.Deps) {
      // already PRE-ACCEPTED, no point looking for conflicts again
      return false, replica, instance
    }
  }
  for q := int32(0); q < int32(e.R.N); q++ {
    for i := e.ExecedUpTo[q]; i < e.crtInstance[q]; i++ {
      if replica == q && instance == i {
        // no point checking past instance in replica's row, since replica would have
        // set the dependencies correctly for anything started after instance
        break
      }
      if i == deps[q] {
        //the instance cannot be a dependency for itself
        continue
      }
      inst := e.InstanceSpace[q][i]
      if inst == nil || inst.Cmds == nil || len(inst.Cmds) == 0 {
        continue
      }
      if inst.Deps[replica] >= instance {
        // instance q.i depends on instance replica.instance, it is not a conflict
        continue
      }
      if state.ConflictBatch(inst.Cmds, cmds) {
        dlog.Printf("%d.%d has commands that conflict with %d.%d.\n", q, i, instance, seq)
        if i > deps[q] ||
          (i < deps[q] && inst.Seq >= seq && (q != replica || inst.Status > epaxosproto.PREACCEPTED_EQ)) {
          // this is a conflict
          return true, q, i
        }
      }
    }
  }
  return false, -1, -1
}

func (e *EPaxosRMWHandler) handleTryPreAcceptReply(tpar *epaxosproto.TryPreAcceptReply) {
  inst := e.InstanceSpace[tpar.Replica][tpar.Instance]
  if inst == nil || inst.lb == nil || !inst.lb.tryingToPreAccept || inst.lb.recoveryInst == nil {
    return
  }

  ir := inst.lb.recoveryInst

  if tpar.OK == TRUE {
    inst.lb.preAcceptOKs++
    inst.lb.tpaOKs++
    if inst.lb.preAcceptOKs >= e.R.N/2 {
      //it's safe to start Accept phase
      inst.Cmds = ir.cmds
      inst.Seq = ir.seq
      gooseCopy13 := ir.deps // verification workaround (T1): copy through a local
      inst.Deps = gooseCopy13
      gooseCopy1 := ir.base // verification workaround (T1): copy through a local
      inst.Base = gooseCopy1
      inst.Status = epaxosproto.ACCEPTED
      inst.vbal = inst.ballot // fix (G16): the recovering replica accepts the value at its ballot
      inst.lb.tryingToPreAccept = false
      inst.lb.acceptOKs = 0
      e.bcastAccept(tpar.Replica, tpar.Instance, inst.ballot, inst.Cmds, inst.Seq, inst.Deps, inst.Base)
      return
    }
  } else {
    inst.lb.nacks++
    if tpar.Ballot > inst.ballot {
      //TODO: retry with higher ballot
      return
    }
    inst.lb.tpaOKs++
    if tpar.ConflictReplica == tpar.Replica && tpar.ConflictInstance == tpar.Instance {
      //TODO: re-run prepare
      inst.lb.tryingToPreAccept = false
      return
    }
    inst.lb.possibleQuorum[tpar.AcceptorId] = false
    inst.lb.possibleQuorum[tpar.ConflictReplica] = false
    notInQuorum := 0
    for q := 0; q < e.R.N; q++ {
      if !inst.lb.possibleQuorum[tpar.AcceptorId] {
        notInQuorum++
      }
    }
    if tpar.ConflictStatus >= epaxosproto.COMMITTED || notInQuorum > e.R.N/2 {
      //abandon recovery, restart from phase 1
      inst.lb.tryingToPreAccept = false
      e.startPhase1(tpar.Replica, tpar.Instance, inst.ballot, inst.lb.clientProposals, ir.cmds, len(ir.cmds))
    }
    if notInQuorum == e.R.N/2 {
      //this is to prevent defer cycles
      if present, dq, _ := deferredByInstance(tpar.Replica, tpar.Instance); present {
        if inst.lb.possibleQuorum[dq] {
          //an instance whose leader must have been in this instance's quorum has been deferred for this instance => contradiction
          //abandon recovery, restart from phase 1
          inst.lb.tryingToPreAccept = false
          e.startPhase1(tpar.Replica, tpar.Instance, inst.ballot, inst.lb.clientProposals, ir.cmds, len(ir.cmds))
        }
      }
    }
    if inst.lb.tpaOKs >= e.R.N/2 {
      //defer recovery and update deferred information
      updateDeferred(tpar.Replica, tpar.Instance, tpar.ConflictReplica, tpar.ConflictInstance)
      inst.lb.tryingToPreAccept = false
    }
  }
}

func (e *EPaxosRMWHandler) executeOverwrite(eo *ExecuteOverwrite) {
  e.R.HandleOverwrite(eo.K, eo.V, eo.T)
  executed := &gryffproto.Executed{eo.Leader, eo.Slot}
  if eo.Leader == e.R.Id {
    // we are the leader
    dlog.Printf("Executed own instance %d.%d.\n", eo.Leader, eo.Slot)
    e.handleExecuted(executed)
  } else {
    // notify the leader we executed
    e.replyExecuted(eo.Leader, executed)
  }
}

func (e *EPaxosRMWHandler) handleExecuted(ex *gryffproto.Executed) {
  inst := e.InstanceSpace[ex.Replica][ex.Instance]
  if inst == nil || inst.lb == nil {
    return
  }
  e.incrementNumReplicasExecuted(inst)
}


//helper functions and structures to prevent defer cycles while recovering

var deferMap map[uint64]uint64 = make(map[uint64]uint64)

func updateDeferred(dr int32, di int32, r int32, i int32) {
  daux := (uint64(dr) << 32) | uint64(di)
  aux := (uint64(r) << 32) | uint64(i)
  deferMap[aux] = daux
}

func deferredByInstance(q int32, i int32) (bool, int32, int32) {
  aux := (uint64(q) << 32) | uint64(i)
  daux, present := deferMap[aux]
  if !present {
    return false, 0, 0
  }
  dq := int32(daux >> 32)
  di := int32(daux)
  return true, dq, di
}

func (e *EPaxosRMWHandler) incrementNumReplicasExecuted(w *Instance) {
  atomic.AddInt32(&w.lb.numReplicasExecuted, 1)
  if !w.lb.repliedClient && w.lb.numReplicasExecuted >= int32(e.R.N / 2 + 1) {
    dlog.Printf("%d executed %d.%d. Repsponding to client.\n", w.lb.numReplicasExecuted,
        w.Leader, w.Slot)
    w.lb.repliedClient = true
    // fix (G43): the reply answers the client's own proposal (its expected value); the leader's
    // copy may still hold another value (e.g. an accepted no-op) while the chosen one executed
    e.R.completeRMWWriter(w.lb.clientProposals[0].CommandId,
      w.lb.clientProposals[0].Reply, w.lb.clientProposals[0].Command.OldValue)
  }
}
