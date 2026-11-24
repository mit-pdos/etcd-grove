---- MODULE TraceKit ----
\* tracekit: the model-independent parts of live trace checking. Programs
\* report their steps (durable writes, messages, role changes) to one
\* collector, which writes a single ordered stream; TLC reads the stream as
\* it grows and requires each event to be a step of a TLA+ model. The check
\* fails at the first event the model cannot take.
\*   go/sink.go             Sink: Do announces a durable write, then makes it;
\*                          Emit reports a step. Blocks until the collector has it.
\*   driver/trace.rs        collector and check runner for a Rust test driver;
\*                          verdicts become Antithesis assertions.
\*   check/streamcheck.py   runs TLC on a growing stream; prints ACCEPTED,
\*                          REJECTED k, VIOLATED k or ERROR.
\*   check/replay.py        feeds a recorded stream to the checker, for testing.
\*   stream/TraceKit.java   TLC overrides of StreamEvent and Note.
\*   tools/                 TLC jars (not committed).
\*
\* A program reports a message when it sends or answers it, possibly after
\* reading the state it was built from; the model must allow sending at any
\* later time, as a network delay would.
\*
\* A trace spec built on this module follows four conventions:
\* 1. One cursor, one model state per event. A variable holds the index of
\*    the next event; each step takes StreamEvent of it and requires the
\*    action the event stands for. TLC (breadth first, one worker) stops
\*    when no state can take the next event.
\* 2. Composite steps, no search. An event that implies a model action with
\*    no event of its own is written as that action followed by the event's.
\* 3. Writes are announced before they are made, and applied at once. After
\*    a kill only the last announced write is uncertain; the spec keeps
\*    LastWrite to take it back if the state reported after restart says so.
\* 4. Facts may be forgotten if every guard only tests their presence in a
\*    growing set: dropping facts can only disable steps, so a wrong choice
\*    can only cause a false rejection, never a false acceptance.
\*
\* Limit: TLC allows 65,535 states per behaviour, so a stream must end
\* before that many events.
EXTENDS Naturals, Sequences

\* The i-th event of the stream. Placeholder: TLC uses the Java override
\* (stream/TraceKit.java), which blocks until the event exists and returns
\* [e |-> "End"] after the stream has ended.
StreamEvent(i) == CHOOSE ev : TRUE

Has(ev, field) == field \in DOMAIN ev

\* TRUE; records that the step for event i did the named thing. The Java
\* override appends "i name" once to TRACE_PROGRESS.notes. Put it last in a
\* step so it is evaluated only for steps taken.
Note(name, i) == TRUE

\* A process's durable state before its last announced write (a record the
\* trace spec chooses); <<>> when there is nothing to take back.
NoWrite == <<>>
LastWrite(pre) == <<pre>>
====
