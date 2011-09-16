define(["agda.frp.signal","agda.frp.time"],function(signal,time) { return {
    // Re-export agda.frp.signal
    constant: signal.constant,
    zero: signal.zero,
    one: signal.one,
    heartbeat: signal.heartbeat,
    empty: signal.empty,
    geolocation: signal.geolocation,
    reactimate: signal.reactimate,
    // Re-export agda.frp.time
    seconds: time.seconds,
    minutes: time.minutes,
    hours: time.hours,
    every: time.every,
    date: time.date
}; });