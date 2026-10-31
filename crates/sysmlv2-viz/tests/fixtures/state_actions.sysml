package S {
	action def Chore;
	action def Log;
	attribute def Sig;
	part p;
	action refuel;
	state def Machine {
		entry; then idle;
		state idle {
			entry action warm;
			do refuel;
			exit action bye : Log;
		}
		state busy {
			do action { sweep : Chore; polish; }
			exit send new Sig() to p;
		}
		state waiting { do; exit; }
	}
	state def Idle { do; exit; }
	requirement def Bare { subject; actor; }
}
