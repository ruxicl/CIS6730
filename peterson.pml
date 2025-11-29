// Peterson's mutual exclusion protocol

//This is the protocol we developed in class.
bit flags[2] = {0, 0};
byte turn;

active[2] proctype proc() 
{
    try:
        flags[_pid] = 1; //Say "I want to enter"
        turn = 1 - _pid; //Say "The other process can go first, if it wants to"
        (turn == _pid || flags[1 - _pid] == 0); //Wait either for my turn, or for the other process to not want to enter
    crit: 
        skip;
    leave: 
        flags[_pid] = 0; //Say "I am not in the critical section anymore"
    goto try //Try again to enter the critical section    
}

ltl inv {
    [] (! (proc[0]@crit && proc[1]@crit ) ) //mutual exclusion
    && [](<> (proc[0]@crit)) //starvation freedom only passes with the -f flag
    && [](<> (proc[1]@crit)) 
}