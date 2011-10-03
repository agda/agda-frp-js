// A top-level module for running test suites.
require(["qunit.js"],function() {
    function run(tests) {
	var visitor = {
	    "ε": function() {},
	    "_,_": function(test1,test2) { test1(visitor); test2(visitor); },
	    "ok": function(name,value) { ok(value,name); },
	    "ok!": function(name,value) { ok(value,name); },
	    "test": function(name,tests) { test(name,function() { tests(visitor); }); },
	    "suite": function(name,tests) { module(name); tests(visitor); }
	};
	tests(visitor);
    }
    // Find scripts with a data-agda tag.
    if (document) { require.ready(function() {
	var scripts = document.getElementsByTagName("script");
	for (var i = 0 ; i < scripts.length; i++) {
	    var agdaName = scripts[i].getAttribute("data-agda");
	    var agdaTests = scripts[i].getAttribute("data-agda-tests") || "tests";
	    if (agdaName) {
		var jsName = "jAgda." + agdaName;
		require([jsName],function(jsModule) {
		    var jsTests = jsModule[agdaTests];
		    run(jsTests);
		});
	    }
	}
    }); }
});