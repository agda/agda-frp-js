// A mixin function, which copies its own properties to a target.

define(function () { 
    function mixin(obj) {
	for (key in this) {
	    if (this.hasOwnProperty(key)) { 
		obj[key] = this[key];
	    }
	}
	return obj;
    }
    return {
	singleton: { mixin: mixin }
    };
});
