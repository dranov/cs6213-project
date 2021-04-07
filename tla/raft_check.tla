--------------------------------- MODULE raft_check ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS 
    \* @type: Set(Int);
    Server

\* Server states.
CONSTANTS 
    \* @type: Str;
    Follower,
    \* @type: Str;
    Candidate,
    \* @type: Str;
    Leader

\* A reserved value.
CONSTANTS 
    \* @type: Int;
    Nil

\* Message types:
CONSTANTS 
    \* @type: Str;
    RequestVoteRequest,
    \* @type: Str;
    RequestVoteResponse,
    \* @type: Str;
    AppendEntriesRequest,
    \* @type: Str;
    AppendEntriesResponse
          
\* Maximum number of client requests
CONSTANTS 
    \* @type: Int;
    MaxClientRequests

EmptyRVReqMsg == [
    mtype         |-> RequestVoteRequest,
    mterm         |-> Nil,
    mlastLogTerm  |-> Nil,
    mlastLogIndex |-> Nil,
    msource       |-> Nil,
    mdest         |-> Nil
]

EmptyRVRespMsg == [
    mtype        |-> RequestVoteResponse,
    mterm        |-> Nil,
    mvoteGranted |-> FALSE,
    mlog         |-> << >>,
    msource      |-> Nil,
    mdest        |-> Nil
]

EmptyAEReqMsg == [
    mtype          |-> AppendEntriesRequest,
    mterm          |-> Nil,
    mprevLogIndex  |-> Nil,
    mprevLogTerm   |-> Nil,
    mentries       |-> << >>,
    mlog           |-> << >>,
    mcommitIndex   |-> Nil,
    msource        |-> Nil,
    mdest          |-> Nil
]

EmptyAERespMsg == [
    mtype           |-> AppendEntriesResponse,
    mterm           |-> Nil,
    msuccess        |-> FALSE,
    mmatchIndex     |-> Nil,
    msource         |-> Nil,
    mdest           |-> Nil
]

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. We differentiate between the message types to support Apalache.
VARIABLE
    \* @typeAlias: ENTRY = [term: Int, value: Int];
    \* @typeAlias: LOGT = Seq(ENTRY);
    \* @typeAlias: RVREQT = [mtype: Str, mterm: Int, mlastLogTerm: Int, mlastLogIndex: Int, msource: Int, mdest: Int];
    \* @typeAlias: RVRESPT = [mtype: Str, mterm: Int, mvoteGranted: Bool, mlog: LOGT, msource: Int, mdest: Int ];
    \* @typeAlias: AEREQT = [mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: LOGT, mlog: LOGT, mcommitIndex: Int, msource: Int, mdest: Int ];
    \* @typeAlias: AERESPT = [mtype: Str, mterm: Int, msuccess: Bool, mmatchIndex: Int, msource: Int, mdest: Int ];
    \* @typeAlias: MSG = [ wrapped: Bool, mtype: Str, mterm: Int, msource: Int, mdest: Int, RVReq: RVREQT, RVResp: RVRESPT, AEReq: AEREQT, AEResp: AERESPT ];
    \* @type: MSG -> Int;
    messages

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE 
    \* @type: Set([ eterm: Int, eleader: Int, elog: LOGT, evotes: Set(Int), evoterLog: (Int -> LOGT) ]);
    elections

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of every log ever in the system (set of logs).
VARIABLE 
    \* @type: Set(t);
    allLogs

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE
    \* @type: Int -> Int;
    currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE
    \* @type: Int -> Str;
    state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE
    \* @type: Int -> Int;
    votedFor
serverVars == <<currentTerm, state, votedFor>>

\* The set of requests that can go into the log
VARIABLE 
    \* @type: Int;
    clientRequests

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE
    \* @type: Int -> LOGT;
    log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE 
    \* @type: Int -> Int;
    commitIndex
\* The index that gets committed
VARIABLE 
    \* @type: LOGT;
    committedLog
\* Does the commited Index decrease
VARIABLE 
    \* @type: Bool;
    committedLogDecrease
logVars == <<log, commitIndex, clientRequests, committedLog, committedLogDecrease >>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE 
    \* @type: Int -> Bool;
    votesSent
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE 
    \* @type: Int -> Set(Int);
    votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE 
    \* @type: Int -> (Int -> LOGT);
    voterLog
candidateVars == <<votesSent, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE 
    \* @type: Int -> (Int -> Int);
    nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE 
    \* @type: Int -> (Int -> Int);
    matchIndex
leaderVars == <<nextIndex, matchIndex, elections>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
\* @type: (Seq([term: Int, value: Int])) => Int;
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
\* @type: (a, a -> Int) => a -> Int;
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2 ]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
\* @type: (a, a -> Int) => a -> Int;
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0 ]
    ELSE
        msgs
        
ValidMessage(msgs) ==
    { m \in DOMAIN messages : msgs[m] > 0 }
    
SingleMessage(msgs) ==
    { m \in DOMAIN messages : msgs[m] = 1 } 

\* @type: a => MSG;
WrapMsg(m) == 
    IF "wrapped" \notin DOMAIN m THEN
        IF m.mtype = RequestVoteRequest THEN
            [ wrapped |-> TRUE, mtype |-> m.mtype, mterm |-> m.mterm, msource |-> m.msource, mdest |-> m.mdest, RVReq |-> m, RVResp |-> EmptyRVRespMsg, AEReq |-> EmptyAEReqMsg, AEResp |-> EmptyAERespMsg ]
        ELSE IF m.mtype = RequestVoteResponse THEN
            [ wrapped |-> TRUE, mtype |-> m.mtype, mterm |-> m.mterm, msource |-> m.msource, mdest |-> m.mdest, RVReq |-> EmptyRVReqMsg, RVResp |-> m, AEReq |-> EmptyAEReqMsg, AEResp |-> EmptyAERespMsg ]
        ELSE IF m.type = AppendEntriesRequest THEN
            [ wrapped |-> TRUE, mtype |-> m.mtype, mterm |-> m.mterm, msource |-> m.msource, mdest |-> m.mdest, RVReq |-> EmptyRVReqMsg, RVResp |-> EmptyRVReqMsg, AEReq |-> m, AEResp |-> EmptyAERespMsg ]
        ELSE
            [ wrapped |-> TRUE, mtype |-> m.mtype, mterm |-> m.mterm, msource |-> m.msource, mdest |-> m.mdest, RVReq |-> EmptyRVReqMsg, RVResp |-> EmptyRVReqMsg, AEReq |-> EmptyAEReqMsg, AEResp |-> m ]
    ELSE m

\* Add a message to the bag of messages.
\* @type: a => Bool;
Send(m) == 
    LET w == WrapMsg(m) IN
    messages' = WithMessage(w, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) ==
    LET w == WrapMsg(m) IN
    messages' = WithoutMessage(w, messages)

\* Combination of Send and Discard
Reply(response, request) ==
    LET wreq == WrapMsg(request) IN
    LET wresp == WrapMsg(response) IN
    messages' = WithoutMessage(wreq, WithMessage(wresp, messages))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----

\* Define initial values for all variables

InitHistoryVars == /\ elections = {}
                   /\ allLogs   = {}
                   /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesSent = [i \in Server |-> FALSE ]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
               /\ clientRequests = 1
               /\ committedLog = << >>
               /\ committedLogDecrease = FALSE
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
\* @type: Int => Bool;
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesSent'      = [votesSent EXCEPT ![i] = FALSE ]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections, clientRequests, committedLog, committedLogDecrease>>

\* Server i times out and starts a new election.
\* @type: Int => Bool;
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesSent' = [votesSent EXCEPT ![i] = FALSE ]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars>>

\* Candidate i sends j a RequestVote request.
\* @type: (Int, Int) => Bool;
RequestVote(i,j) ==
    /\ state[i] = Candidate
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, votesGranted, voterLog, leaderVars, logVars, votesSent>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
\* @type: (Int, Int) => Bool;
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                msource        |-> i,
                mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Candidate i transitions to leader.
\* @type: Int => Bool;
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ elections'  = elections \cup
                         {[eterm     |-> currentTerm[i],
                           eleader   |-> i,
                           elog      |-> log[i],
                           evotes    |-> votesGranted[i],
                           evoterLog |-> voterLog[i]]}
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars>>

\* Leader i receives a client request to add v to the log.
\* @type: Int => Bool;
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ clientRequests < MaxClientRequests
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> clientRequests]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]
           \* Make sure that each request is unique, reduce state space to be explored
           /\ clientRequests' = clientRequests + 1
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex, committedLog, committedLogDecrease>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
\* @type: Int => Bool;
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
           newCommittedLog ==
              IF newCommitIndex > 1 THEN 
                \* [ j \in 1..newCommitIndex |-> log[i][j] ]
                SubSeq(log[i], 1, newCommitIndex)
              ELSE 
                   << >>
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          /\ committedLogDecrease' = \/ ( newCommitIndex < Len(committedLog) )
                                     \/ \E j \in 1..Len(committedLog) : committedLog[j] /= newCommittedLog[j]
          /\ committedLog' = newCommittedLog
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, clientRequests>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* @type: (Int, Int, RVREQT) => Bool;
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
\* @type: (Int, Int, RVRESPT) => Bool;
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
        \*   /\ UNCHANGED <<votesSent>>
        \* work-around Apalache model checker quirk
          /\ votesSent' = votesSent
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesSent, votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
\* @type: (Int, Int, AEREQT) => Bool;
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              m.mcommitIndex]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, logVars>>
                   \/ \* conflict: remove 1 entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                    \*    /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |-> log[i][index2]]
                       /\ LET new == SubSeq(log[i], 1, Len(log[i]) - 1)
                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, clientRequests, committedLog, committedLogDecrease>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries[1])]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, clientRequests, committedLog, committedLogDecrease>>
       /\ UNCHANGED <<candidateVars, leaderVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
\* @type: (Int, Int, AERESPT) => Bool;
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
        \*   /\ UNCHANGED <<matchIndex>>
          /\ matchIndex' = matchIndex
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, elections>>

\* Any RPC with a newer term causes the recipient to advance its term first.
\* @type: (Int, Int, MSG) => Bool;
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>

\* Responses with stale terms are ignored.
\* @type: (Int, Int, MSG) => Bool;
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Receive a message.
\* @type: MSG => Bool;
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m.RVReq)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m.RVResp)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m.AEReq)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m.AEResp)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

----
\* Defines how the variables may transition.
Next == /\ \/ \E i \in Server : Restart(i)
           \/ \E i \in Server : Timeout(i)
           \/ \E i, j \in Server : RequestVote(i, j)
           \/ \E i \in Server : BecomeLeader(i)
           \/ \E i \in Server : ClientRequest(i)
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : AppendEntries(i, j)
           \/ \E m \in ValidMessage(messages) : Receive(m)
           \/ \E m \in SingleMessage(messages) : DuplicateMessage(m)
           \/ \E m \in ValidMessage(messages) : DropMessage(m)
           \* History variable that tracks every log ever:
        /\ allLogs' = allLogs \cup {log[i] : i \in Server}

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

\* The following are a set of verification by jinlmsft@hotmail.com
BothLeader(i, j) == 
    /\ i /= j
    /\ currentTerm[i] = currentTerm[j]
    /\ state[i] = Leader
    /\ state[j] = Leader

MoreThanOneLeader ==
    \E i, j \in Server : BothLeader(i, j) 


\* Properties from Figure 3 in the Raft paper
ElectionSafety == ~ MoreThanOneLeader
LeaderAppendOnly == ~ committedLogDecrease

LogMatching ==
    \A i, j \in Server:
    \A matchingIndex \in 1..Min({Len(log[i]), Len(log[j])}):
        log[i][matchingIndex].term = log[j][matchingIndex].term =>
            (\A idx \in 1..matchingIndex : log[i][idx] = log[j][idx])

LeaderCompleteness ==
    \* If a log entry is committed in a given term
    \A n \in Server:
    \A idx \in 1..MaxClientRequests:
        LET entry == log[n][idx] IN
        commitIndex[n] >= idx =>
        \* Then that entry will be present in the logs of the leaders of all higher terms
        []
        (\A l \in Server:
            /\ state[l] = Leader
            /\ currentTerm[l] >= entry.term
            => (\E index \in 1..Len(log[l]) : log[l][index] = entry)
        )

Test == \A i \in Server: commitIndex[i] <= 0
Test2 == \A i \in Server: Len(log[i]) <= 0

===============================================================================

\* Changelog:
\*
\* 2016-08-23
\* - Make the model more suitable for model checking. See
\*   https://github.com/ongardie/raft.tla/pull/4/
\* 
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation
