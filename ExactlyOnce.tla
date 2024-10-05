---- MODULE ExactlyOnce ----

EXTENDS Sequences, Integers

CONSTANT NULL

VARIABLES InputTopic, Buffer, OutputTopic, CommittedConsumerOffset, PC, CurrentToken, Token, RemainingRestarts

vars == <<InputTopic, Buffer, OutputTopic, CommittedConsumerOffset, PC, CurrentToken, Token, RemainingRestarts>>

Processes == {1, 2}

Init ==
    /\ InputTopic = <<1>>
    /\ Buffer = [ process \in Processes |-> NULL ]
    /\ OutputTopic = <<>>
    /\ CommittedConsumerOffset = 1
    /\ PC = [ process \in Processes |-> "AcquireToken" ]
    /\ CurrentToken = 0
    /\ Token = [ process \in Processes |-> NULL ]
    /\ RemainingRestarts = [ process \in Processes |-> 1 ]

MessagesAvailable == CommittedConsumerOffset < Len(InputTopic) + 1

Update(function, x, y) == [ function EXCEPT ![x] = y ]

AcquireToken(process) ==
    /\ PC[process] = "AcquireToken"
    /\ CurrentToken' = CurrentToken + 1
    /\ Token' = Update(Token, process, CurrentToken')
    /\ PC' = Update(PC, process, "Consume")
    /\ UNCHANGED <<InputTopic, Buffer, OutputTopic, CommittedConsumerOffset, RemainingRestarts>>

Consume(process) ==
    /\ PC[process] = "Consume"
    /\ IF MessagesAvailable
       THEN /\ Buffer' = Update(Buffer, process, InputTopic[CommittedConsumerOffset])
            /\ PC' = Update(PC, process, "ProduceCommit")
       ELSE /\ Buffer' = Update(Buffer, process, NULL)
            /\ PC' = Update(PC, process, "Done")
    /\ UNCHANGED <<InputTopic, OutputTopic, CommittedConsumerOffset, CurrentToken, Token, RemainingRestarts>>

ProduceCommit(process) ==
    /\ PC[process] = "ProduceCommit"
    /\ IF Token[process] = CurrentToken
       THEN /\ OutputTopic' = Append(OutputTopic, Buffer[process])
            /\ CommittedConsumerOffset' = Buffer[process] + 1
            /\ PC' = Update(PC, process, "Consume")
            /\ UNCHANGED <<InputTopic, Buffer, CurrentToken, Token, RemainingRestarts>>
       ELSE /\ PC' = Update(PC, process, "Fenced")
            /\ UNCHANGED <<InputTopic, Buffer, OutputTopic, CommittedConsumerOffset, CurrentToken, Token, RemainingRestarts>>

Fenced(process) ==
    /\ PC[process] = "Fenced"
    /\ UNCHANGED vars

Done(process) ==
    /\ PC[process] = "Done"
    /\ UNCHANGED vars

Restart(process) ==
    /\ PC[process] \notin {"Fenced", "Done"}
    /\ RemainingRestarts[process] > 0
    /\ Buffer' = Update(Buffer, process, NULL)
    /\ PC' = Update(PC, process, "AcquireToken")
    /\ RemainingRestarts' = Update(RemainingRestarts, process, RemainingRestarts[process] - 1)
    /\ UNCHANGED <<InputTopic, OutputTopic, CommittedConsumerOffset, CurrentToken, Token>>

Next ==
    \E process \in Processes:
        \/ AcquireToken(process)
        \/ Consume(process)
        \/ ProduceCommit(process)
        \/ Restart(process)
        \/ Fenced(process)
        \/ Done(process)

Fairness ==
    \E process \in Processes:
        /\ WF_vars(Next)
        /\ SF_vars(ProduceCommit(process))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

Termination == <>[](\A process \in Processes: PC[process] \in {"Fenced", "Done"})

NoDuplicatesIn(seq) ==
    \A i, j \in 1..Len(seq):
        i /= j => seq[i] /= seq[j]

NoDuplicates == NoDuplicatesIn(OutputTopic)

SeqContains(seq, value) ==
    \E x \in 1..Len(seq):
        seq[x] = value

SeqContainsAll(seq, values) ==
    \A i \in 1..Len(values):
        SeqContains(seq, values[i])

NoMissingData == <>[](SeqContainsAll(OutputTopic, InputTopic))

====
