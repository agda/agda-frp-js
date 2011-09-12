require(["../js/agda-frp"],function(frp) { require.ready(function () {
    function utcTime(now) { return new Date(now).toUTCString(); };
    var clock = 
      frp.seconds()     // The current time with 1-second accuracy
        .map(utcTime)   // Convert to a string in UTC format
        .text()         // Convert to an HTML text node
        .element("p");  // Embed in an HTML <p> node
    clock.attachTo(document.getElementById("root"));
}); });
