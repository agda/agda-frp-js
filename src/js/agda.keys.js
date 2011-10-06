define(["agda.mixin"],function(mixin) {
    function IKeys(array,offset) {
	this.array = array;
	this.offset = offset;
    }
    mixin.singleton.mixin(IKeys.prototype);
    IKeys.prototype.key = function() {
	return this.array[this.offset];
    }
    IKeys.prototype.tail = function() {	
	return new IKeys(this.array,this.offset+1);
    }
    IKeys.prototype.cons = function(x) {
	var offset = this.offset - 1;
	var array = this.array;
	if (offset < 0) {
	    offset = Math.min(1024,array.length+1);
	    array = new Array(offset).concat(array);
	} else if (array[offset] !== undefined) {
	    if (array[offset] === x) { return this; }
	    array = new Array(offset).concat(array.slice(offset));
	}
	array[offset] = x;
	return new IKeys(array,offset);
    }
    IKeys.prototype.size = function() {
	return this.array.length - this.offset;
    }
    IKeys.prototype.keys = function() {
	if (this.offset > 0) {
	    this.array = this.array.slice(this.offset);
	    this.offset = 0;
	}
	return this.array;
    }
    return {
	IKeys: IKeys,
	iarray: function(array) { return new IKeys(array,0); },
	iempty: new IKeys([],0)
    };
});