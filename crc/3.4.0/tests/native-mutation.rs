// Diagnostic observation, not a contract asserting that mutation is supported.
#[test]
fn public_algorithm_reassignment_observation() {
    static A: Algorithm<u8> = Algorithm {width:8,poly:7,init:0,refin:false,refout:false,xorout:0,check:0,residue:0};
    static B: Algorithm<u8> = Algorithm {poly:0x31,..A};
    macro_rules! observe { ($lane:literal,$expected:literal) => {{
       let mut changed=Crc::<u8,Table<$lane>>::new(&A); changed.algorithm=&B;
       let fresh=Crc::<u8,Table<$lane>>::new(&B);
       assert_eq!(fresh.checksum(&[1]),0x31);
       assert_eq!(changed.checksum(&[1]),$expected);
       println!("public algorithm reassignment lane={}: changed={:#04x}, fresh={:#04x}",$lane,changed.checksum(&[1]),fresh.checksum(&[1]));
    }}; }
    observe!(0,0x31); observe!(1,0x07); observe!(16,0x07);
}
