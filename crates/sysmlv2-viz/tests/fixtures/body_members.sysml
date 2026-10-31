package BodyMembers {
	private import ScalarValues::*;
	part def Vehicle { attribute mass : Real; }
	part def Driver;
	part def Sensor;
	port def FuelPort { in item fuel : Fuel; }
	item def Fuel;
	concern def Safety { subject v : Vehicle; stakeholder driver : Driver; }
	concern safety : Safety;
	requirement def MassLimit {
		doc /* The vehicle mass shall not exceed the limit. */
		subject vehicle : Vehicle;
		actor operator : Driver;
		stakeholder owner : Driver;
		in attribute limit : Real;
		attribute margin : Real;
		assume constraint fueled { vehicle.mass > 0 }
		require constraint underLimit { vehicle.mass <= limit }
		frame concern worry : Safety;
		requirement sub : MassLimit;
	}
	requirement massReq : MassLimit { subject vehicle : Vehicle; }
	constraint def UnderLimit { in attribute m : Real; in attribute limit : Real; m <= limit }
	calc def Total { in attribute a : Real; in attribute b : Real; return attribute sum : Real; a + b }
	use case def Drive { subject vehicle : Vehicle; actor driver : Driver; objective { doc /* Arrive. */ } include use case park; }
	use case park;
	analysis def MassAnalysis {
		subject vehicle : Vehicle;
		objective massObjective { require constraint { vehicle.mass < 2000 } }
		return attribute totalMass : Real;
		vehicle.mass
	}
	verification def MassTest {
		subject vehicle : Vehicle;
		objective { verify requirement massReq; }
		return verdict : VerificationCases::VerdictKind;
		action weigh;
	}
	action refuel;
	state def Engine { entry action warm; do refuel; exit action cool; state off; state on; transition first off then on; }
	interface def FuelLine { end port src : FuelPort; end port dst : ~FuelPort; }
	connection def Mount { end part car : Vehicle; end part sensor : Sensor; }
	part car : Vehicle { satisfy massReq by car; }
	viewpoint def Ops { frame safety; stakeholder driver : Driver; }
}
