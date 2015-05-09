/**
*   \file data/title_tiles.inc
*   \brief Tiles and maps used for the menu frame, title screen logo, and cursor
*   \author kivan117 (James Elliott)
*   \date 2015
*/

/*
 * Transformation file: title_tiles.xml
 * Source image: title_tiles.png
 * Tile width: 8px
 * Tile height: 8px
 * Output format: (null)
 */
#define TITLE_GH_WIDTH 6
#define TITLE_GH_HEIGHT 4
const char title_gh[] PROGMEM ={
6,4
,0xb,0xc,0xd,0xe,0xf,0x10,0x17,0x18,0x19,0x1a,0x1b,0x1c,0x25,0x26,0x27,0x28,0x29,0x1c,0x30,0x31
,0x32,0x33,0x34,0x35};

#define TITLE_ST_WIDTH 5
#define TITLE_ST_HEIGHT 4
const char title_st[] PROGMEM ={
5,4
,0xb,0x11,0x12,0xc,0x13,0x1d,0x1e,0x1f,0x20,0x21,0x2a,0x2b,0x2c,0x2d,0x2c,0x36,0x37,0x38,0x39,0x38};

#define TITLE_Y_WIDTH 3
#define TITLE_Y_HEIGHT 4
const char title_y[] PROGMEM ={
3,4
,0x14,0x15,0x16,0x22,0x23,0x24,0x2e,0x2f,0x1,0x34,0x3a,0x1};

#define TITLE_MOON_WIDTH 3
#define TITLE_MOON_HEIGHT 3
const char title_moon[] PROGMEM ={
3,3
,0x3b,0x3c,0x1,0x3d,0x1,0x3e,0x40,0x41,0x42};

#define TITLE_O_WIDTH 3
#define TITLE_O_HEIGHT 4
const char title_o[] PROGMEM ={
3,4
,0xb,0x11,0x2c,0x1d,0x3f,0x2c,0x43,0x3f,0x2c,0x36,0x37,0x38};

#define TITLE_TILES_SIZE 68
const char title_tiles[] PROGMEM={
 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:0
, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:1
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0xad, 0xad, 0xad, 0xad, 0xad, 0x41, 0x41, 0x41, 0xad, 0xa4, 0xa4, 0xad, 0xad, 0x41, 0x41, 0x41, 0xa4, 0xa4, 0xa4, 0xa4, 0xad, 0xad, 0xad, 0x41, 0x53, 0xa4, 0xa4, 0xa4, 0xad, 0xa4, 0xa4, 0x41, 0x53, 0x53, 0xa4, 0xa4, 0xad, 0x0, 0x0, 0x41, 0x41, 0x41, 0xa4, 0xad, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0xa4, 0xad, 0x0, 0x0, 0x0		 //tile:2
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0xad, 0xad, 0xad, 0xad, 0xad, 0x41, 0x41, 0x41, 0xad, 0xa4, 0xa4, 0xad, 0xad, 0x41, 0xad, 0xad, 0xa4, 0xa4, 0xa4, 0xa4, 0xad, 0x41, 0xa4, 0xa4, 0x53, 0xa4, 0xa4, 0xa4, 0xad, 0x41, 0x0, 0x0, 0x53, 0x53, 0xa4, 0xa4, 0xad, 0x41, 0x0, 0x0, 0x0, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0xa4, 0xad, 0x41, 0x41, 0x41		 //tile:3
, 0x41, 0x41, 0x41, 0xa4, 0xad, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0xa4, 0xad, 0x0, 0x0, 0x0, 0x41, 0xad, 0xad, 0xad, 0xad, 0xad, 0x0, 0x0, 0x41, 0xad, 0xa4, 0xa4, 0xad, 0xad, 0xad, 0xad, 0x41, 0xa4, 0xa4, 0xa4, 0xa4, 0xad, 0xa4, 0xa4, 0x41, 0x53, 0xa4, 0xa4, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x53, 0x53, 0xa4, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:4
, 0x0, 0x0, 0x0, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x0, 0x0, 0xad, 0xad, 0xad, 0xad, 0xad, 0x41, 0xad, 0xad, 0xad, 0xa4, 0xa4, 0xad, 0xad, 0x41, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x53, 0xa4, 0xa4, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x53, 0x53, 0xa4, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:5
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0xad, 0xad, 0xad, 0xad, 0xad, 0xad, 0xad, 0xad, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:6
, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xad, 0xad, 0xad, 0xad, 0xad, 0xad, 0xad, 0xad, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:7
, 0x41, 0x41, 0x41, 0xa4, 0xad, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0xa4, 0xad, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0xa4, 0xad, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0xa4, 0xad, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0xa4, 0xad, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0xa4, 0xad, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0xa4, 0xad, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0xa4, 0xad, 0x0, 0x0, 0x0		 //tile:8
, 0x0, 0x0, 0x0, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0xa4, 0xad, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0xa4, 0xad, 0x41, 0x41, 0x41		 //tile:9
, 0xad, 0xad, 0xad, 0xad, 0xad, 0x0, 0x0, 0x0, 0xad, 0xad, 0xad, 0xad, 0xad, 0xad, 0x0, 0x0, 0xad, 0xa4, 0xa4, 0xa4, 0xad, 0xad, 0xad, 0x0, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0xad, 0xad, 0xad, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0xad, 0xad, 0xa4, 0xa4, 0xa4, 0xa4, 0xa4, 0x53, 0x53, 0x0, 0x53, 0xa4, 0xa4, 0xa4, 0x53, 0x53, 0x0, 0x0, 0x53, 0x53, 0x53, 0x53, 0x53, 0x0, 0x0, 0x0		 //tile:10
, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:11
, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:12
, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94		 //tile:13
, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0		 //tile:14
, 0x94, 0x0, 0x0, 0x0, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x94, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41		 //tile:15
, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:16
, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:17
, 0x94, 0x0, 0x0, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41		 //tile:18
, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0		 //tile:19
, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:20
, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:21
, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:22
, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94		 //tile:23
, 0x41, 0x94, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94		 //tile:24
, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x94		 //tile:25
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:26
, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:27
, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:28
, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:29
, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:30
, 0x94, 0x0, 0x0, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:31
, 0x94, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:32
, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:33
, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41		 //tile:34
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0		 //tile:35
, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:36
, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:37
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:38
, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94		 //tile:39
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0		 //tile:40
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41		 //tile:41
, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94		 //tile:42
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:43
, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:44
, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:45
, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41		 //tile:46
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0		 //tile:47
, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:48
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:49
, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:50
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:51
, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x41, 0x41, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:52
, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x41, 0x41, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:53
, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:54
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:55
, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:56
, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x0, 0x0, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:57
, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x0, 0x0, 0x94, 0x94, 0x94, 0x94, 0x94, 0x94, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:58
, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbf, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0		 //tile:59
, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:60
, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf		 //tile:61
, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbf, 0x0		 //tile:62
, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41		 //tile:63
, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:64
, 0xbf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0		 //tile:65
, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0x0, 0xbf, 0xbf, 0xbf, 0x0, 0x0, 0x0, 0x0, 0x0, 0xbf, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0		 //tile:66
, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94, 0x94, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x94		 //tile:67
};