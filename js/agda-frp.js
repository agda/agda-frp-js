define(["./agda-frp-signal","./agda-frp-time"],function(signal,time) { return {
    // Re-export agda-frp-signal
    constant: signal.constant,
    zero: signal.zero,
    one: signal.one,
    heartbeat: signal.heartbeat,
    empty: signal.empty,
    // Re-export agda-frp-time
    seconds: time.seconds,
    minutes: time.minutes,
    hours: time.hours
}; });