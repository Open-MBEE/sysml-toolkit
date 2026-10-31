package U {
	part def Tank { action fill; }
	part tank : Tank;
	item def Go;
	state def Engine {
		entry 'provide power';
		do tank.drain;
		exit Ops::park;
		state on;
		state off;
		transition first on accept Go do 'shut down' then off;
		transition first off accept Go do tank.fill then on;
	}
	part car { exhibit 'car states'; }
	requirement def Limit { require 'mass limit'; }
}
package A {
	part def Tank { action fill; }
	part tank : Tank;
	action def Run {
		perform 'warm up';
		perform tank.drain;
		perform tank.fill;
	}
}
package E {
	part def Tank { action fill; }
	part tank : Tank;
	state idle;
	use case trip;
	part car {
		perform tank.drain;
		perform tank.fill;
		exhibit idle.missing;
	}
	use case def Drive {
		include 'add fuel';
		include trip.missing;
	}
}
package N {
	port def M;
	interface def I { end port a : M; end port b : M; }
	part def Tank { action fill; port mount : M; }
	part tank : Tank;
	requirement spec;
	part car {
		perform tank.fill;
		perform tank.drain;
		perform 'warm up';
		perform 'cool down' [2];
		exhibit 'some state';
		satisfy spec;
		satisfy 'missing spec';
		event 'some event';
		part ::> tank;
		part ::> 'spare tank';
		interface : I connect tank.missing to tank.mount;
	}
}
