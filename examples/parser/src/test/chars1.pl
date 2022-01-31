/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 7/13/95, 4:54 PM */
/* Filename: chars1.pl */
/* Abstract: The class of a character. Version with facts. The predicate
char_class/2 is used in tokens.pl . */

char_class(-1,end_of_file).
char_class(0,illegal).
char_class(1,illegal).
char_class(2,illegal).
char_class(3,illegal).
char_class(4,illegal).
char_class(5,illegal).
char_class(6,illegal).
char_class(7,illegal).
char_class(8,layout(space)).			% BS back space
char_class(9,layout(space)).			% HT horizontal tab
char_class(10,layout(new_line)).		% NL new line
char_class(11,layout(space)).			% VT vertical tab
char_class(12,layout(space)).			% NP new page, form feed
char_class(13,layout(new_line)).		% CR carriage return
char_class(14,illegal).
char_class(15,illegal).
char_class(16,illegal).
char_class(17,illegal).
char_class(18,illegal).
char_class(19,illegal).
char_class(20,illegal).
char_class(21,illegal).
char_class(22,illegal).
char_class(23,illegal).
char_class(24,illegal).
char_class(25,illegal).
char_class(26,end_of_file).			% MacOS ???
char_class(27,illegal).
char_class(28,illegal).
char_class(29,illegal).
char_class(30,illegal).
char_class(31,layout(new_line)).		% US MacOS ??? (return)
char_class(32,layout(space)).			% SP space
char_class(33,solo(name(!))). 			% !
char_class(34,double_quote). 			% "
char_class(35,graphic(plain)). 			% #
char_class(36,graphic(plain)). 			% $
char_class(37,end_line_comment). 		% %
char_class(38,graphic(plain)). 			% &
char_class(39,single_quote). 			% '
char_class(40,solo(open(layout))). 		% (
char_class(41,solo(close)). 			% )
char_class(42,graphic(comment_2)). 		% *
char_class(43,graphic(plain)). 			% +
char_class(44,solo(comma)). 			% ,
char_class(45,graphic(plain)). 			% -
char_class(46,graphic(end)). 			% .
char_class(47,graphic(comment_1)). 		% /
char_class(48,alpha_num(decimal_digit)). 	% 0
char_class(49,alpha_num(decimal_digit)). 	% 1
char_class(50,alpha_num(decimal_digit)). 	% 2
char_class(51,alpha_num(decimal_digit)). 	% 3
char_class(52,alpha_num(decimal_digit)). 	% 4
char_class(53,alpha_num(decimal_digit)). 	% 5
char_class(54,alpha_num(decimal_digit)). 	% 6
char_class(55,alpha_num(decimal_digit)). 	% 7
char_class(56,alpha_num(decimal_digit)). 	% 8
char_class(57,alpha_num(decimal_digit)). 	% 9
char_class(58,graphic(plain)). 			% :
char_class(59,solo(name(;))). 			% ;
char_class(60,graphic(plain)). 			% <
char_class(61,graphic(plain)). 			% =
char_class(62,graphic(plain)). 			% >
char_class(63,graphic(plain)). 			% ?
char_class(64,graphic(plain)). 			% @
char_class(65,alpha_num(capital_letter)). 	% A
char_class(66,alpha_num(capital_letter)). 	% B
char_class(67,alpha_num(capital_letter)). 	% C
char_class(68,alpha_num(capital_letter)). 	% D
char_class(69,alpha_num(capital_letter)). 	% E
char_class(70,alpha_num(capital_letter)). 	% F
char_class(71,alpha_num(capital_letter)). 	% G
char_class(72,alpha_num(capital_letter)). 	% H
char_class(73,alpha_num(capital_letter)). 	% I
char_class(74,alpha_num(capital_letter)). 	% J
char_class(75,alpha_num(capital_letter)). 	% K
char_class(76,alpha_num(capital_letter)). 	% L
char_class(77,alpha_num(capital_letter)). 	% M
char_class(78,alpha_num(capital_letter)). 	% N
char_class(79,alpha_num(capital_letter)). 	% O
char_class(80,alpha_num(capital_letter)). 	% P
char_class(81,alpha_num(capital_letter)). 	% Q
char_class(82,alpha_num(capital_letter)). 	% R
char_class(83,alpha_num(capital_letter)). 	% S
char_class(84,alpha_num(capital_letter)). 	% T
char_class(85,alpha_num(capital_letter)). 	% U
char_class(86,alpha_num(capital_letter)). 	% V
char_class(87,alpha_num(capital_letter)). 	% W
char_class(88,alpha_num(capital_letter)). 	% X
char_class(89,alpha_num(capital_letter)). 	% Y
char_class(90,alpha_num(capital_letter)). 	% Z
char_class(91,solo(open_list)). 		% [
char_class(92,graphic(backslash)). 		% \
char_class(93,solo(close_list)). 		% ]
char_class(94,graphic(plain)). 			% ^
char_class(95,alpha_num(capital_letter)). 	% _
char_class(96,back_quote). 			% `
char_class(97,alpha_num(small_letter)). 	% a
char_class(98,alpha_num(small_letter)). 	% b
char_class(99,alpha_num(small_letter)). 	% c
char_class(100,alpha_num(small_letter)). 	% d
char_class(101,alpha_num(small_letter)). 	% e
char_class(102,alpha_num(small_letter)). 	% f
char_class(103,alpha_num(small_letter)). 	% g
char_class(104,alpha_num(small_letter)). 	% h
char_class(105,alpha_num(small_letter)). 	% i
char_class(106,alpha_num(small_letter)). 	% j
char_class(107,alpha_num(small_letter)). 	% k
char_class(108,alpha_num(small_letter)). 	% l
char_class(109,alpha_num(small_letter)). 	% m
char_class(110,alpha_num(small_letter)). 	% n
char_class(111,alpha_num(small_letter)). 	% o
char_class(112,alpha_num(small_letter)). 	% p
char_class(113,alpha_num(small_letter)). 	% q
char_class(114,alpha_num(small_letter)). 	% r
char_class(115,alpha_num(small_letter)). 	% s
char_class(116,alpha_num(small_letter)). 	% t
char_class(117,alpha_num(small_letter)). 	% u
char_class(118,alpha_num(small_letter)). 	% v
char_class(119,alpha_num(small_letter)). 	% w
char_class(120,alpha_num(small_letter)). 	% x
char_class(121,alpha_num(small_letter)). 	% y
char_class(122,alpha_num(small_letter)). 	% z
char_class(123,solo(open_curly)). 		% {
char_class(124,solo(head_tail_sep)). 		% |
char_class(125,solo(close_curly)). 		% }
char_class(126,graphic(plain)). 		% ~
char_class(127,illegal). 			% DEL
char_class(128,illegal).
char_class(129,illegal).
char_class(130,illegal).
char_class(131,illegal).
char_class(132,illegal).
char_class(133,illegal).
char_class(134,illegal).
char_class(135,illegal).
char_class(136,illegal).
char_class(137,illegal).
char_class(138,illegal).
char_class(139,illegal).
char_class(140,illegal).
char_class(141,illegal).
char_class(142,illegal).
char_class(143,illegal).
char_class(144,illegal).
char_class(145,illegal).
char_class(146,illegal).
char_class(147,illegal).
char_class(148,illegal).
char_class(149,illegal).
char_class(150,illegal).
char_class(151,illegal).
char_class(152,illegal).
char_class(153,illegal).
char_class(154,illegal).
char_class(155,illegal).
char_class(156,illegal).
char_class(157,illegal).
char_class(158,illegal).
char_class(159,illegal).
char_class(160,illegal).
char_class(161,illegal).
char_class(162,illegal).
char_class(163,illegal).
char_class(164,illegal).
char_class(165,illegal).
char_class(166,illegal).
char_class(167,illegal).
char_class(168,illegal).
char_class(169,illegal).
char_class(170,illegal).
char_class(171,illegal).
char_class(172,illegal).
char_class(173,illegal).
char_class(174,illegal).
char_class(175,illegal).
char_class(176,illegal).
char_class(177,illegal).
char_class(178,illegal).
char_class(179,illegal).
char_class(180,illegal).
char_class(181,illegal).
char_class(182,illegal).
char_class(183,illegal).
char_class(184,illegal).
char_class(185,illegal).
char_class(186,illegal).
char_class(187,illegal).
char_class(188,illegal).
char_class(189,illegal).
char_class(190,illegal).
char_class(191,illegal).
char_class(192,illegal).
char_class(193,illegal).
char_class(194,illegal).
char_class(195,illegal).
char_class(196,illegal).
char_class(197,illegal).
char_class(198,illegal).
char_class(199,illegal).
char_class(200,illegal).
char_class(201,illegal).
char_class(202,illegal).
char_class(203,illegal).
char_class(204,illegal).
char_class(205,illegal).
char_class(206,illegal).
char_class(207,illegal).
char_class(208,illegal).
char_class(209,illegal).
char_class(210,illegal).
char_class(211,illegal).
char_class(212,illegal).
char_class(213,illegal).
char_class(214,illegal).
char_class(215,illegal).
char_class(216,illegal).
char_class(217,illegal).
char_class(218,illegal).
char_class(219,illegal).
char_class(220,illegal).
char_class(221,illegal).
char_class(222,illegal).
char_class(223,illegal).
char_class(224,illegal).
char_class(225,illegal).
char_class(226,illegal).
char_class(227,illegal).
char_class(228,illegal).
char_class(229,illegal).
char_class(230,illegal).
char_class(231,illegal).
char_class(232,illegal).
char_class(233,illegal).
char_class(234,illegal).
char_class(235,illegal).
char_class(236,illegal).
char_class(237,illegal).
char_class(238,illegal).
char_class(239,illegal).
char_class(240,illegal).
char_class(241,illegal).
char_class(242,illegal).
char_class(243,illegal).
char_class(244,illegal).
char_class(245,illegal).
char_class(246,illegal).
char_class(247,illegal).
char_class(248,illegal).
char_class(249,illegal).
char_class(250,illegal).
char_class(251,illegal).
char_class(252,illegal).
char_class(253,illegal).
char_class(254,illegal).
char_class(255,illegal).

% End of chars1.pl

