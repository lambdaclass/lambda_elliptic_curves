use super::Fp;
pub const ALPHA: u64 = 7;
pub const ALPHA_INV: u64 = 10540996611094048183;

// Constants obtained using the paper implementation in Sage
// https://github.com/ASDiscreteMathematics/rpo/tree/master/reference_implementation

// Constants for the 128-bit security level
pub const MDS_VECTOR_128: [Fp; 12] = [
    Fp::const_from_raw(7),
    Fp::const_from_raw(23),
    Fp::const_from_raw(8),
    Fp::const_from_raw(26),
    Fp::const_from_raw(13),
    Fp::const_from_raw(10),
    Fp::const_from_raw(9),
    Fp::const_from_raw(7),
    Fp::const_from_raw(6),
    Fp::const_from_raw(22),
    Fp::const_from_raw(21),
    Fp::const_from_raw(8),
];
pub const ROUND_CONSTANTS_128: [Fp; 168] = [
    Fp::const_from_raw(5789762306288267392),
    Fp::const_from_raw(6522564764413701783),
    Fp::const_from_raw(17809893479458208203),
    Fp::const_from_raw(107145243989736508),
    Fp::const_from_raw(6388978042437517382),
    Fp::const_from_raw(15844067734406016715),
    Fp::const_from_raw(9975000513555218239),
    Fp::const_from_raw(3344984123768313364),
    Fp::const_from_raw(9959189626657347191),
    Fp::const_from_raw(12960773468763563665),
    Fp::const_from_raw(9602914297752488475),
    Fp::const_from_raw(16657542370200465908),
    Fp::const_from_raw(6077062762357204287),
    Fp::const_from_raw(15277620170502011191),
    Fp::const_from_raw(5358738125714196705),
    Fp::const_from_raw(14233283787297595718),
    Fp::const_from_raw(13792579614346651365),
    Fp::const_from_raw(11614812331536767105),
    Fp::const_from_raw(14871063686742261166),
    Fp::const_from_raw(10148237148793043499),
    Fp::const_from_raw(4457428952329675767),
    Fp::const_from_raw(15590786458219172475),
    Fp::const_from_raw(10063319113072092615),
    Fp::const_from_raw(14200078843431360086),
    Fp::const_from_raw(12987190162843096997),
    Fp::const_from_raw(653957632802705281),
    Fp::const_from_raw(4441654670647621225),
    Fp::const_from_raw(4038207883745915761),
    Fp::const_from_raw(5613464648874830118),
    Fp::const_from_raw(13222989726778338773),
    Fp::const_from_raw(3037761201230264149),
    Fp::const_from_raw(16683759727265180203),
    Fp::const_from_raw(8337364536491240715),
    Fp::const_from_raw(3227397518293416448),
    Fp::const_from_raw(8110510111539674682),
    Fp::const_from_raw(2872078294163232137),
    Fp::const_from_raw(6202948458916099932),
    Fp::const_from_raw(17690140365333231091),
    Fp::const_from_raw(3595001575307484651),
    Fp::const_from_raw(373995945117666487),
    Fp::const_from_raw(1235734395091296013),
    Fp::const_from_raw(14172757457833931602),
    Fp::const_from_raw(707573103686350224),
    Fp::const_from_raw(15453217512188187135),
    Fp::const_from_raw(219777875004506018),
    Fp::const_from_raw(17876696346199469008),
    Fp::const_from_raw(17731621626449383378),
    Fp::const_from_raw(2897136237748376248),
    Fp::const_from_raw(18072785500942327487),
    Fp::const_from_raw(6200974112677013481),
    Fp::const_from_raw(17682092219085884187),
    Fp::const_from_raw(10599526828986756440),
    Fp::const_from_raw(975003873302957338),
    Fp::const_from_raw(8264241093196931281),
    Fp::const_from_raw(10065763900435475170),
    Fp::const_from_raw(2181131744534710197),
    Fp::const_from_raw(6317303992309418647),
    Fp::const_from_raw(1401440938888741532),
    Fp::const_from_raw(8884468225181997494),
    Fp::const_from_raw(13066900325715521532),
    Fp::const_from_raw(8023374565629191455),
    Fp::const_from_raw(15013690343205953430),
    Fp::const_from_raw(4485500052507912973),
    Fp::const_from_raw(12489737547229155153),
    Fp::const_from_raw(9500452585969030576),
    Fp::const_from_raw(2054001340201038870),
    Fp::const_from_raw(12420704059284934186),
    Fp::const_from_raw(355990932618543755),
    Fp::const_from_raw(9071225051243523860),
    Fp::const_from_raw(12766199826003448536),
    Fp::const_from_raw(9045979173463556963),
    Fp::const_from_raw(12934431667190679898),
    Fp::const_from_raw(5674685213610121970),
    Fp::const_from_raw(5759084860419474071),
    Fp::const_from_raw(13943282657648897737),
    Fp::const_from_raw(1352748651966375394),
    Fp::const_from_raw(17110913224029905221),
    Fp::const_from_raw(1003883795902368422),
    Fp::const_from_raw(4141870621881018291),
    Fp::const_from_raw(8121410972417424656),
    Fp::const_from_raw(14300518605864919529),
    Fp::const_from_raw(13712227150607670181),
    Fp::const_from_raw(17021852944633065291),
    Fp::const_from_raw(6252096473787587650),
    Fp::const_from_raw(18389244934624494276),
    Fp::const_from_raw(16731736864863925227),
    Fp::const_from_raw(4440209734760478192),
    Fp::const_from_raw(17208448209698888938),
    Fp::const_from_raw(8739495587021565984),
    Fp::const_from_raw(17000774922218161967),
    Fp::const_from_raw(13533282547195532087),
    Fp::const_from_raw(525402848358706231),
    Fp::const_from_raw(16987541523062161972),
    Fp::const_from_raw(5466806524462797102),
    Fp::const_from_raw(14512769585918244983),
    Fp::const_from_raw(10973956031244051118),
    Fp::const_from_raw(4887609836208846458),
    Fp::const_from_raw(3027115137917284492),
    Fp::const_from_raw(9595098600469470675),
    Fp::const_from_raw(10528569829048484079),
    Fp::const_from_raw(7864689113198939815),
    Fp::const_from_raw(17533723827845969040),
    Fp::const_from_raw(5781638039037710951),
    Fp::const_from_raw(17024078752430719006),
    Fp::const_from_raw(109659393484013511),
    Fp::const_from_raw(7158933660534805869),
    Fp::const_from_raw(2955076958026921730),
    Fp::const_from_raw(7433723648458773977),
    Fp::const_from_raw(6982293561042362913),
    Fp::const_from_raw(14065426295947720331),
    Fp::const_from_raw(16451845770444974180),
    Fp::const_from_raw(7139138592091306727),
    Fp::const_from_raw(9012006439959783127),
    Fp::const_from_raw(14619614108529063361),
    Fp::const_from_raw(1394813199588124371),
    Fp::const_from_raw(4635111139507788575),
    Fp::const_from_raw(16217473952264203365),
    Fp::const_from_raw(10782018226466330683),
    Fp::const_from_raw(6844229992533662050),
    Fp::const_from_raw(7446486531695178711),
    Fp::const_from_raw(16308865189192447297),
    Fp::const_from_raw(11977192855656444890),
    Fp::const_from_raw(12532242556065780287),
    Fp::const_from_raw(14594890931430968898),
    Fp::const_from_raw(7291784239689209784),
    Fp::const_from_raw(5514718540551361949),
    Fp::const_from_raw(10025733853830934803),
    Fp::const_from_raw(7293794580341021693),
    Fp::const_from_raw(6728552937464861756),
    Fp::const_from_raw(6332385040983343262),
    Fp::const_from_raw(13277683694236792804),
    Fp::const_from_raw(2600778905124452676),
    Fp::const_from_raw(3736792340494631448),
    Fp::const_from_raw(577852220195055341),
    Fp::const_from_raw(6689998335515779805),
    Fp::const_from_raw(13886063479078013492),
    Fp::const_from_raw(14358505101923202168),
    Fp::const_from_raw(7744142531772274164),
    Fp::const_from_raw(16135070735728404443),
    Fp::const_from_raw(12290902521256031137),
    Fp::const_from_raw(12059913662657709804),
    Fp::const_from_raw(16456018495793751911),
    Fp::const_from_raw(4571485474751953524),
    Fp::const_from_raw(17200392109565783176),
    Fp::const_from_raw(7123075680859040534),
    Fp::const_from_raw(1034205548717903090),
    Fp::const_from_raw(7717824418247931797),
    Fp::const_from_raw(3019070937878604058),
    Fp::const_from_raw(11403792746066867460),
    Fp::const_from_raw(10280580802233112374),
    Fp::const_from_raw(337153209462421218),
    Fp::const_from_raw(13333398568519923717),
    Fp::const_from_raw(3596153696935337464),
    Fp::const_from_raw(8104208463525993784),
    Fp::const_from_raw(14345062289456085693),
    Fp::const_from_raw(17036731477169661256),
    Fp::const_from_raw(17130398059294018733),
    Fp::const_from_raw(519782857322261988),
    Fp::const_from_raw(9625384390925085478),
    Fp::const_from_raw(1664893052631119222),
    Fp::const_from_raw(7629576092524553570),
    Fp::const_from_raw(3485239601103661425),
    Fp::const_from_raw(9755891797164033838),
    Fp::const_from_raw(15218148195153269027),
    Fp::const_from_raw(16460604813734957368),
    Fp::const_from_raw(9643968136937729763),
    Fp::const_from_raw(3611348709641382851),
    Fp::const_from_raw(18256379591337759196),
];

pub const MDS_MATRIX_128: [[Fp; 12]; 12] = [
    [
        Fp::const_from_raw(7),
        Fp::const_from_raw(23),
        Fp::const_from_raw(8),
        Fp::const_from_raw(26),
        Fp::const_from_raw(13),
        Fp::const_from_raw(10),
        Fp::const_from_raw(9),
        Fp::const_from_raw(7),
        Fp::const_from_raw(6),
        Fp::const_from_raw(22),
        Fp::const_from_raw(21),
        Fp::const_from_raw(8),
    ],
    [
        Fp::const_from_raw(8),
        Fp::const_from_raw(7),
        Fp::const_from_raw(23),
        Fp::const_from_raw(8),
        Fp::const_from_raw(26),
        Fp::const_from_raw(13),
        Fp::const_from_raw(10),
        Fp::const_from_raw(9),
        Fp::const_from_raw(7),
        Fp::const_from_raw(6),
        Fp::const_from_raw(22),
        Fp::const_from_raw(21),
    ],
    [
        Fp::const_from_raw(21),
        Fp::const_from_raw(8),
        Fp::const_from_raw(7),
        Fp::const_from_raw(23),
        Fp::const_from_raw(8),
        Fp::const_from_raw(26),
        Fp::const_from_raw(13),
        Fp::const_from_raw(10),
        Fp::const_from_raw(9),
        Fp::const_from_raw(7),
        Fp::const_from_raw(6),
        Fp::const_from_raw(22),
    ],
    [
        Fp::const_from_raw(22),
        Fp::const_from_raw(21),
        Fp::const_from_raw(8),
        Fp::const_from_raw(7),
        Fp::const_from_raw(23),
        Fp::const_from_raw(8),
        Fp::const_from_raw(26),
        Fp::const_from_raw(13),
        Fp::const_from_raw(10),
        Fp::const_from_raw(9),
        Fp::const_from_raw(7),
        Fp::const_from_raw(6),
    ],
    [
        Fp::const_from_raw(6),
        Fp::const_from_raw(22),
        Fp::const_from_raw(21),
        Fp::const_from_raw(8),
        Fp::const_from_raw(7),
        Fp::const_from_raw(23),
        Fp::const_from_raw(8),
        Fp::const_from_raw(26),
        Fp::const_from_raw(13),
        Fp::const_from_raw(10),
        Fp::const_from_raw(9),
        Fp::const_from_raw(7),
    ],
    [
        Fp::const_from_raw(7),
        Fp::const_from_raw(6),
        Fp::const_from_raw(22),
        Fp::const_from_raw(21),
        Fp::const_from_raw(8),
        Fp::const_from_raw(7),
        Fp::const_from_raw(23),
        Fp::const_from_raw(8),
        Fp::const_from_raw(26),
        Fp::const_from_raw(13),
        Fp::const_from_raw(10),
        Fp::const_from_raw(9),
    ],
    [
        Fp::const_from_raw(9),
        Fp::const_from_raw(7),
        Fp::const_from_raw(6),
        Fp::const_from_raw(22),
        Fp::const_from_raw(21),
        Fp::const_from_raw(8),
        Fp::const_from_raw(7),
        Fp::const_from_raw(23),
        Fp::const_from_raw(8),
        Fp::const_from_raw(26),
        Fp::const_from_raw(13),
        Fp::const_from_raw(10),
    ],
    [
        Fp::const_from_raw(10),
        Fp::const_from_raw(9),
        Fp::const_from_raw(7),
        Fp::const_from_raw(6),
        Fp::const_from_raw(22),
        Fp::const_from_raw(21),
        Fp::const_from_raw(8),
        Fp::const_from_raw(7),
        Fp::const_from_raw(23),
        Fp::const_from_raw(8),
        Fp::const_from_raw(26),
        Fp::const_from_raw(13),
    ],
    [
        Fp::const_from_raw(13),
        Fp::const_from_raw(10),
        Fp::const_from_raw(9),
        Fp::const_from_raw(7),
        Fp::const_from_raw(6),
        Fp::const_from_raw(22),
        Fp::const_from_raw(21),
        Fp::const_from_raw(8),
        Fp::const_from_raw(7),
        Fp::const_from_raw(23),
        Fp::const_from_raw(8),
        Fp::const_from_raw(26),
    ],
    [
        Fp::const_from_raw(26),
        Fp::const_from_raw(13),
        Fp::const_from_raw(10),
        Fp::const_from_raw(9),
        Fp::const_from_raw(7),
        Fp::const_from_raw(6),
        Fp::const_from_raw(22),
        Fp::const_from_raw(21),
        Fp::const_from_raw(8),
        Fp::const_from_raw(7),
        Fp::const_from_raw(23),
        Fp::const_from_raw(8),
    ],
    [
        Fp::const_from_raw(8),
        Fp::const_from_raw(26),
        Fp::const_from_raw(13),
        Fp::const_from_raw(10),
        Fp::const_from_raw(9),
        Fp::const_from_raw(7),
        Fp::const_from_raw(6),
        Fp::const_from_raw(22),
        Fp::const_from_raw(21),
        Fp::const_from_raw(8),
        Fp::const_from_raw(7),
        Fp::const_from_raw(23),
    ],
    [
        Fp::const_from_raw(23),
        Fp::const_from_raw(8),
        Fp::const_from_raw(26),
        Fp::const_from_raw(13),
        Fp::const_from_raw(10),
        Fp::const_from_raw(9),
        Fp::const_from_raw(7),
        Fp::const_from_raw(6),
        Fp::const_from_raw(22),
        Fp::const_from_raw(21),
        Fp::const_from_raw(8),
        Fp::const_from_raw(7),
    ],
];

// Constants for the 160-bit security level

pub const MDS_VECTOR_160: [Fp; 16] = [
    Fp::const_from_raw(256),
    Fp::const_from_raw(2),
    Fp::const_from_raw(1073741824),
    Fp::const_from_raw(2048),
    Fp::const_from_raw(16777216),
    Fp::const_from_raw(128),
    Fp::const_from_raw(8),
    Fp::const_from_raw(16),
    Fp::const_from_raw(524288),
    Fp::const_from_raw(4194304),
    Fp::const_from_raw(1),
    Fp::const_from_raw(268435456),
    Fp::const_from_raw(1),
    Fp::const_from_raw(1024),
    Fp::const_from_raw(2),
    Fp::const_from_raw(8192),
];

pub const ROUND_CONSTANTS_160: [Fp; 224] = [
    Fp::const_from_raw(1965335827333385572),
    Fp::const_from_raw(13386940263093285890),
    Fp::const_from_raw(2676433512518024499),
    Fp::const_from_raw(3265387569419834752),
    Fp::const_from_raw(1983410871005483133),
    Fp::const_from_raw(9697282293408698131),
    Fp::const_from_raw(1272774544215511539),
    Fp::const_from_raw(8206289606243220511),
    Fp::const_from_raw(1290391036756663400),
    Fp::const_from_raw(18219831014774660739),
    Fp::const_from_raw(9691367064095402927),
    Fp::const_from_raw(1323942862844130786),
    Fp::const_from_raw(15151407902520044968),
    Fp::const_from_raw(3367241195349533752),
    Fp::const_from_raw(4045613938354522492),
    Fp::const_from_raw(8414577515806306591),
    Fp::const_from_raw(12735791373473705278),
    Fp::const_from_raw(3301196190123345788),
    Fp::const_from_raw(4934538150586227609),
    Fp::const_from_raw(3817643842607407527),
    Fp::const_from_raw(13416431558822898318),
    Fp::const_from_raw(5832629091408730901),
    Fp::const_from_raw(3362368740314001033),
    Fp::const_from_raw(11092906639494490385),
    Fp::const_from_raw(6071859273097876791),
    Fp::const_from_raw(10161425034618716356),
    Fp::const_from_raw(7152209120756903545),
    Fp::const_from_raw(16380870469663741149),
    Fp::const_from_raw(3952136951542576078),
    Fp::const_from_raw(17537441052343611097),
    Fp::const_from_raw(11551242553047556263),
    Fp::const_from_raw(10106900133850428740),
    Fp::const_from_raw(11416650542216810040),
    Fp::const_from_raw(11422270812969046329),
    Fp::const_from_raw(8866991719313052084),
    Fp::const_from_raw(11055863001411088108),
    Fp::const_from_raw(6180770262849183127),
    Fp::const_from_raw(15065904341621422463),
    Fp::const_from_raw(6379231142859676194),
    Fp::const_from_raw(12898133478008807755),
    Fp::const_from_raw(17022976567648776965),
    Fp::const_from_raw(9092326911543756291),
    Fp::const_from_raw(6030122978628466915),
    Fp::const_from_raw(9597034755157312926),
    Fp::const_from_raw(994741965321505508),
    Fp::const_from_raw(7556490651023083151),
    Fp::const_from_raw(13471961853484783473),
    Fp::const_from_raw(5530500298270693480),
    Fp::const_from_raw(3138602747749119790),
    Fp::const_from_raw(14959768162492908516),
    Fp::const_from_raw(9134218270579160311),
    Fp::const_from_raw(11526344086740032769),
    Fp::const_from_raw(18056157006815181954),
    Fp::const_from_raw(6800589288408907691),
    Fp::const_from_raw(15936640138392473876),
    Fp::const_from_raw(2300163192580995689),
    Fp::const_from_raw(4526841916921293676),
    Fp::const_from_raw(7195881155996340935),
    Fp::const_from_raw(2785483023916634674),
    Fp::const_from_raw(15081468567893261932),
    Fp::const_from_raw(6614707290651872269),
    Fp::const_from_raw(13681365294828420351),
    Fp::const_from_raw(10664658542323360702),
    Fp::const_from_raw(10084964797450915045),
    Fp::const_from_raw(4845198022119750202),
    Fp::const_from_raw(2607866667643628253),
    Fp::const_from_raw(5208104371714885253),
    Fp::const_from_raw(12959011109386888563),
    Fp::const_from_raw(4000466944391262442),
    Fp::const_from_raw(17728719744160665330),
    Fp::const_from_raw(7150641948246037689),
    Fp::const_from_raw(9776810486328380322),
    Fp::const_from_raw(8402715679168885485),
    Fp::const_from_raw(3121448252217290414),
    Fp::const_from_raw(17436789549778885163),
    Fp::const_from_raw(15165907014487612788),
    Fp::const_from_raw(11269595316481578714),
    Fp::const_from_raw(9914651255870961898),
    Fp::const_from_raw(12689101348845299684),
    Fp::const_from_raw(11975655653136929369),
    Fp::const_from_raw(7372192115875804252),
    Fp::const_from_raw(374526648312709133),
    Fp::const_from_raw(5985220408386061330),
    Fp::const_from_raw(7185802228951619536),
    Fp::const_from_raw(1399294693953396201),
    Fp::const_from_raw(3261364014951657316),
    Fp::const_from_raw(12077409443637692420),
    Fp::const_from_raw(9673650825325087603),
    Fp::const_from_raw(5569045552142119082),
    Fp::const_from_raw(17617312550416673451),
    Fp::const_from_raw(6211450796053144311),
    Fp::const_from_raw(11274862073326008409),
    Fp::const_from_raw(18367233290057731659),
    Fp::const_from_raw(13198876392118957255),
    Fp::const_from_raw(13272050586507026767),
    Fp::const_from_raw(13010781901687851463),
    Fp::const_from_raw(11176896862794321170),
    Fp::const_from_raw(6638609153583434674),
    Fp::const_from_raw(14505835809704498565),
    Fp::const_from_raw(17581684280975726513),
    Fp::const_from_raw(699795237352602006),
    Fp::const_from_raw(9944038704239459812),
    Fp::const_from_raw(8047212797227008956),
    Fp::const_from_raw(1395744870455664103),
    Fp::const_from_raw(18357515964980248812),
    Fp::const_from_raw(9097466431298056431),
    Fp::const_from_raw(14710664890151992774),
    Fp::const_from_raw(6629781383077611287),
    Fp::const_from_raw(17573797615501516970),
    Fp::const_from_raw(12347664633647440814),
    Fp::const_from_raw(11021709264172808686),
    Fp::const_from_raw(10955032358008028206),
    Fp::const_from_raw(12827014260928926472),
    Fp::const_from_raw(14274600229400487385),
    Fp::const_from_raw(12031986599882032134),
    Fp::const_from_raw(16154104676212634613),
    Fp::const_from_raw(18132152994017433356),
    Fp::const_from_raw(15441239634310983499),
    Fp::const_from_raw(10976597099491887044),
    Fp::const_from_raw(3707145841124002094),
    Fp::const_from_raw(8720928559638383045),
    Fp::const_from_raw(16336200500310468906),
    Fp::const_from_raw(6210805750383775651),
    Fp::const_from_raw(7719884621977079797),
    Fp::const_from_raw(11449042012956416425),
    Fp::const_from_raw(9075619080551251971),
    Fp::const_from_raw(617668424765806231),
    Fp::const_from_raw(12270348236411784037),
    Fp::const_from_raw(6186113401837024523),
    Fp::const_from_raw(15458192282022704662),
    Fp::const_from_raw(3533646002027882636),
    Fp::const_from_raw(7323750725122298699),
    Fp::const_from_raw(17370102587019252090),
    Fp::const_from_raw(1740987243995377904),
    Fp::const_from_raw(10219908189144498973),
    Fp::const_from_raw(1822464913426161699),
    Fp::const_from_raw(13340330593340428766),
    Fp::const_from_raw(11476413915876641735),
    Fp::const_from_raw(10301877462024259119),
    Fp::const_from_raw(17003473479205724655),
    Fp::const_from_raw(10899885430087119072),
    Fp::const_from_raw(2161571014943847810),
    Fp::const_from_raw(10337649388059569402),
    Fp::const_from_raw(1627927149280118935),
    Fp::const_from_raw(981019442244479500),
    Fp::const_from_raw(8080861373146567887),
    Fp::const_from_raw(8033636340692269807),
    Fp::const_from_raw(1747076424940820198),
    Fp::const_from_raw(15430102639810276278),
    Fp::const_from_raw(9286420248392647962),
    Fp::const_from_raw(11497964697936588530),
    Fp::const_from_raw(17639509337065865628),
    Fp::const_from_raw(2160917583540985983),
    Fp::const_from_raw(6735220140815683510),
    Fp::const_from_raw(6183237619116523957),
    Fp::const_from_raw(13347893983048485379),
    Fp::const_from_raw(4087545433624195113),
    Fp::const_from_raw(11701648626105993864),
    Fp::const_from_raw(11913677089736238784),
    Fp::const_from_raw(271004950317860287),
    Fp::const_from_raw(11794070108002091165),
    Fp::const_from_raw(15639064309077629849),
    Fp::const_from_raw(16481734838884572560),
    Fp::const_from_raw(3932918848577657311),
    Fp::const_from_raw(16327200574281469287),
    Fp::const_from_raw(7060041503065075033),
    Fp::const_from_raw(4892761442718320741),
    Fp::const_from_raw(8255275116206368067),
    Fp::const_from_raw(14957838536671021552),
    Fp::const_from_raw(14493715972468567436),
    Fp::const_from_raw(7463718209809697261),
    Fp::const_from_raw(3440982266989812843),
    Fp::const_from_raw(2354199421703013492),
    Fp::const_from_raw(2321628279578256047),
    Fp::const_from_raw(3746041501354899488),
    Fp::const_from_raw(11186576936873825301),
    Fp::const_from_raw(15218587616061641074),
    Fp::const_from_raw(11844784525417523222),
    Fp::const_from_raw(7998727848169056055),
    Fp::const_from_raw(7948968711630609066),
    Fp::const_from_raw(11805042600408037937),
    Fp::const_from_raw(18172588443872800894),
    Fp::const_from_raw(13092373363317372568),
    Fp::const_from_raw(2169983441195298580),
    Fp::const_from_raw(1499680808057735775),
    Fp::const_from_raw(7077486803310915643),
    Fp::const_from_raw(743612288630452727),
    Fp::const_from_raw(11665426394426065172),
    Fp::const_from_raw(15533499373769144802),
    Fp::const_from_raw(14249183160150274240),
    Fp::const_from_raw(13792290235996127743),
    Fp::const_from_raw(4995017088228886738),
    Fp::const_from_raw(9763845271226970122),
    Fp::const_from_raw(1727820159257625458),
    Fp::const_from_raw(9681902124347643227),
    Fp::const_from_raw(11327574568051933160),
    Fp::const_from_raw(10627429556158481577),
    Fp::const_from_raw(13984143774797145216),
    Fp::const_from_raw(17082059622058840713),
    Fp::const_from_raw(16264233536802058333),
    Fp::const_from_raw(10077962488096645822),
    Fp::const_from_raw(5057253598123536060),
    Fp::const_from_raw(2301672207952647376),
    Fp::const_from_raw(17506877517896521554),
    Fp::const_from_raw(14583366393971011156),
    Fp::const_from_raw(6226877164823354372),
    Fp::const_from_raw(2260055134098203623),
    Fp::const_from_raw(12945296184826522120),
    Fp::const_from_raw(15417698598606677168),
    Fp::const_from_raw(7447949755934804788),
    Fp::const_from_raw(8017843736725863212),
    Fp::const_from_raw(1003688007091182795),
    Fp::const_from_raw(8935767355090348282),
    Fp::const_from_raw(793319158990348431),
    Fp::const_from_raw(4437923789992338287),
    Fp::const_from_raw(7869978205237541489),
    Fp::const_from_raw(9039403419111053092),
    Fp::const_from_raw(3845065612997771849),
    Fp::const_from_raw(15179573672801872590),
    Fp::const_from_raw(2879645310341005490),
    Fp::const_from_raw(4421001170561580576),
    Fp::const_from_raw(7614461260369642079),
    Fp::const_from_raw(10869617590371203777),
    Fp::const_from_raw(4582902440098948914),
];

pub const MDS_MATRIX_160: [[Fp; 16]; 16] = [
    [
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
    ],
    [
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
    ],
    [
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
    ],
    [
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
    ],
    [
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
    ],
    [
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
    ],
    [
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
    ],
    [
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
    ],
    [
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
    ],
    [
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
    ],
    [
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
    ],
    [
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
    ],
    [
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
    ],
    [
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
    ],
    [
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
        Fp::const_from_raw(2),
    ],
    [
        Fp::const_from_raw(2),
        Fp::const_from_raw(1073741824),
        Fp::const_from_raw(2048),
        Fp::const_from_raw(16777216),
        Fp::const_from_raw(128),
        Fp::const_from_raw(8),
        Fp::const_from_raw(16),
        Fp::const_from_raw(524288),
        Fp::const_from_raw(4194304),
        Fp::const_from_raw(1),
        Fp::const_from_raw(268435456),
        Fp::const_from_raw(1),
        Fp::const_from_raw(1024),
        Fp::const_from_raw(2),
        Fp::const_from_raw(8192),
        Fp::const_from_raw(256),
    ],
];

#[derive(Clone)]
pub enum SecurityLevel {
    Sec128,
    Sec160,
}

pub fn get_state_size(security_level: &SecurityLevel) -> usize {
    match security_level {
        SecurityLevel::Sec128 => 12,
        SecurityLevel::Sec160 => 16,
    }
}

pub fn get_capacity(security_level: &SecurityLevel) -> usize {
    match security_level {
        SecurityLevel::Sec128 => 4,
        SecurityLevel::Sec160 => 6,
    }
}

pub fn get_round_constants(level: &SecurityLevel) -> &'static [Fp] {
    match level {
        SecurityLevel::Sec128 => &ROUND_CONSTANTS_128,
        SecurityLevel::Sec160 => &ROUND_CONSTANTS_160,
    }
}

pub enum MdsVector {
    Mds128([Fp; 12]),
    Mds160([Fp; 16]),
}

pub fn get_mds_vector(level: SecurityLevel) -> MdsVector {
    match level {
        SecurityLevel::Sec128 => MdsVector::Mds128(MDS_VECTOR_128),
        SecurityLevel::Sec160 => MdsVector::Mds160(MDS_VECTOR_160),
    }
}

#[allow(clippy::large_enum_variant)]
pub enum MdsMatrix {
    Mds128([[Fp; 12]; 12]),
    Mds160([[Fp; 16]; 16]),
}

pub fn get_mds_matrix(level: &SecurityLevel) -> MdsMatrix {
    match level {
        SecurityLevel::Sec128 => MdsMatrix::Mds128(MDS_MATRIX_128),
        SecurityLevel::Sec160 => MdsMatrix::Mds160(MDS_MATRIX_160),
    }
}

impl MdsVector {
    pub fn as_slice(&self) -> &[Fp] {
        match self {
            MdsVector::Mds128(ref vec) => vec,
            MdsVector::Mds160(ref vec) => vec,
        }
    }
}
