// Part 2: Queue Lock Algorithm for NTHREADS = 3
// Use spin -run -f -m1000000 HW2_2.pml

// The modification is in the the atomic get-and-increment block,
// where we now increment cnt and then do mod NTHREADS instead of
// just incrementing (as we did in Part 1). Doing so ensures that
// queue[my_cnt % NTHREADS] (which is now equivalent to simply queue[my_cnt]) 
// and queue[(m_cnt + 1) % NTHREADS] used to read from "queue"
// are atomic (i.e. no process will interfere in between calculating 
// my_cnt % NTHREADS and accessing queue[my_cnt % NTHREADS])
// (This was not a problem previously since the operation x % 2 should be
// by default atomic, regardless of how the size of x).

#define NTHREADS 3

bool queue[NTHREADS] = {1, 0};
byte cnt = 0;

// current number of processes in the critical section 
byte nr_crit_proc = 0;

active [NTHREADS] proctype process() 
{
    byte my_cnt;
    start:
        atomic {
            my_cnt = cnt;
            // necessary change done for NTHREADS = 3 
            cnt = (cnt + 1) % NTHREADS;
        }
    try:
        (queue[my_cnt % NTHREADS] == true);
    crit:
        nr_crit_proc++;
        skip;
    leave:
        queue[my_cnt % NTHREADS] = false;
        nr_crit_proc--;
        queue[(my_cnt + 1) % NTHREADS] = true;
    goto start
}

ltl invariant {
    // mutual exclusion
    [] (nr_crit_proc <= 1)

    // flag slots are used in order
    && [] ((queue[0] == true) -> (!(queue[0] == false && X(queue[0]) == true) U (queue[1] == true)))
    && [] ((queue[0] == true) -> (!(queue[0] == false && X(queue[0]) == true) U (queue[2] == true)))

    && [] ((queue[1] == true) -> (!(queue[1] == false && X(queue[1]) == true) U (queue[2] == true)))
    && [] ((queue[1] == true) -> (!(queue[1] == false && X(queue[1]) == true) U (queue[0] == true)))

    && [] ((queue[2] == true) -> (!(queue[2] == false && X(queue[2]) == true) U (queue[0] == true)))
    && [] ((queue[2] == true) -> (!(queue[2] == false && X(queue[2]) == true) U (queue[1] == true)))

    // starvation freedom
    && [](<> (process[0]@crit)) 
    && [](<> (process[1]@crit))
    && [](<> (process[2]@crit))
}