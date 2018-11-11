//signatures


abstract sig User{
         fiscalCode: one String,
         age: one Int,
         code: one Int,
         sex: one Int ,} //Sarebbe un boolean
	

sig NU extends User{ 	username: one String,
                   position: one Position,
                   follower: set TPU,
                   device: set Device,
                   sosIsActivated: one Int, 
}


 sig TPU extends User{
              bankAccount: one String ,
              companyName: lone String,  
              followedMan: set NU,  //List of the followed normal users
}

sig Date{
	dayNumber: one Int,
	monthNumber: one Int,
	yearNumber: one Int,
	time: one Int, //Sarebbe un Time
}

sig Request {
                     status: one Int,
                     text: one String,
                     sender: one TPU, 
                     receiver: one NU,
                     link: TPU -> NU,
                     date: one Date,
}

sig Position {
		latitude: Int, // should be float
		longitude: Int // should be float
}{
latitude >= 0 and longitude >= 0
}


sig Data {}


sig  Device{
                  user: one NU,
                  data: lone String,
                  code: one Int,
                  }


sig DeviceHandler
                 { device: set Device,}


sig SOS { normalUser: one NU,     
                position: one Position,
                description: one String,}

sig SosHandler {
                 handledSOS: set SOS,
                         }


//FACT


// Data4Help

// I TPU del NU e i NU del TPU sono legati da tabelle date dalle request accettatte
fact CoherentAcceptedRequest {
//Antecedente
all r: Request | all n: NU |all  t: TPU |  r.sender=t &&  r.receiver=n && r.status=1 iff
//Postcedente
n in t.followedMan && t in n.follower
} 

fact CoherentDevice {
//antecedente
all d: Device | all n: NU | d in n.device iff
//Postcedente
n=d.user
}

//Codes are univocal
fact GoodCode {
all u, u': User | all d, d': Device | 
u.code=u'.code iff u=u' and
d.code=d'.code iff d=d'
}

//If a Third Part User follows a normal user, that user is followed by him
fact coherentFollowing {
all n: NU | all  t:TPU |
t in n.follower iff n in t. followedMan
}


fact sosIsActivatedIsBoolean{
all n: NU| n.sosIsActivated=0 or n.sosIsActivated=1
}



//SOS

fact sosIsCorrect {
//antecedente
all n: NU | all s:SOS|
//Postcedente
s.normalUser=n implies s.position=n.position
} // Position of the SOS and of the Data and of the User us be the same, sae fior name nd fiscal code

fact SOSIsHandled {
all s: SOS | one x : SosHandler |
s in x.handledSOS}


//PREDICATI

pred coherentFollowing {
all t: TPU|all n: NU| n in t.followedMan iff t in n.follower
}

pred sendRequest [r, r': Request] {
          r=r+r'
          r'.status = 0
}

pred acceptRequest  [r, r': Request, t, t': TPU, n, n': NU] {
          r'.status = 1
          t'.followedMan=  t.followedMan+r'.receiver
          n'.follower=n.follower+r'.sender
}

pred refuseRequest [r, r': Request,  n, n': NU] {
          r'.status = 0
}

pred addDevice  [d, d': Device, n, n': NU, z, z': DeviceHandler]{
        n'.code=n.code
        d'.code=d.code
        n'.device=n.device+d
        d'.user=n'
        z'.device=z.device+d
     
}

pred removeDevice   [d : Device, n, n': NU, z, z': DeviceHandler]{
              z'.device=z.device-d
              n'.device=n'.device-d
}

pred show(z: DeviceHandler, n: NU, t: TPU, r: Request){
#TPU = 2
#NU = 2
#Request = 2
#Device=3
#SOS=2
#DeviceHandler=1}



//ASSERTIONS


assert removeUndoesAdd{
all z, z', z'': DeviceHandler| all n, n', n'': NU| all d, d': Device|
addDevice [d, d', n, n', z, z'] and removeDevice [d, n', n'', z', z'']
implies
(z.device=z''.device) and (n.device=n''.device)}


//Run and check


run addDevice for 5 but exactly 2 String

run removeDevice for 2

check removeUndoesAdd for 2

run sendRequest for 2 but exactly 4 String 

run show for 1 but exactly 2 String

//Settare l'SOS handler come unico e affarmare che
