// Part 3: The algorithm uses the same idea as Peterson's algorithm, but
// uses bits operations to announce the intention of a process to go to the
// critical section (set the pid of the process-th bit to 1) or to announce
// that it got out of the critical section (set the corresponding bit to 0).

// I think "flag == masks[index]" (the condition that just the current 
// process wants to get in) and potentially other operations are not atomic, 
// so the ltl doesn't hold hold. :(

#define NTHREADS 4

int flags = 0;
byte turn;

int masks[NTHREADS];

// note: this is process 0
init {
    byte i;
    for (i : 0 .. (NTHREADS - 1)) {
        masks[i] = 1 << i;
    }
}

// the processes are now indexed 1 .. NTHREADS
active[NTHREADS] proctype proc() 
{
    byte index = _pid - 1; 
    assert(index < NTHREADS)
    printf("ye: %d \n", index);
    try:
        flags = masks[index] | flags; 
        turn = NTHREADS - _pid; 
        (turn == index || flags == masks[index]);
    crit: 
        skip;
    leave: 
        flags = (~masks[index]) & flags; 
    goto try 
}

ltl inv {
    [] (!(proc[1]@crit && proc[2]@crit)) 
    && [] (<> (proc[1]@crit)) 
    && [] (<> (proc[2]@crit)) 
}