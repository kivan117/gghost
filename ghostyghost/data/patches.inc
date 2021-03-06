/**
*   \file data/patches.inc
*   \brief Sound effect and instrument patches
*   \author kivan117 (James Elliott)
*   \date 2015
*   \author Alec Bourque
*   \date 2008
*/

/*
 *  Uzebox Default Patches
 *  Copyright (C) 2008  Alec Bourque
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

/*
	Patches are made of a command stream made of 3 bytes per command:
		1=delta time
		2=command
		3=command parameter

	Patches must start with 1 byte describing the sound type:
		0=wave channel (i.e.; channel 0,1 and 2)
		1=noise channel (channel 3)
		2=PCM (channel 3)
		->For type=2 two more byte follows in order: sample adress low byte, sample adress hi byte

	It must end with <0,PATCH_END> and this command takes
	only two bytes (no parameter).
*/

//Square Piano
const char patch00[] PROGMEM ={	
0,PC_WAVE,9,
0,PC_ENV_SPEED,-15,  
4,PC_ENV_SPEED,-7,  
0,PATCH_END
};

//Wall Smack
const char patch01[] PROGMEM ={
0,PC_ENV_SPEED,-20,
0,PC_NOISE_PARAMS,2,
1,PC_ENV_VOL,0,
2,PC_ENV_VOL,0x33,
0,PC_NOISE_PARAMS,3,
1,PC_NOTE_CUT,0, 
0,PATCH_END   
};

//Whoosh/Wing Flap
const char patch02[] PROGMEM ={	
0,PC_NOISE_PARAMS,1,
0,PC_ENV_VOL,0x50,
0,PC_ENV_SPEED,-40, 
3,PC_NOTE_CUT,0,
0,PATCH_END
};

//Jump Sound
const char patch03[] PROGMEM ={	
0,PC_ENV_SPEED,-30,
0,PC_WAVE,0,
0,PC_PITCH,55, 
0,PC_SLIDE,10,  
0,PC_SLIDE_SPEED,10, 
8,PC_NOTE_CUT,0,								 
0,PATCH_END
};

//Logo "kling" sound
const char patch04[] PROGMEM ={	
0,PC_WAVE,8,
0,PC_PITCH,85,
4,PC_PITCH,90,
0,PC_ENV_SPEED,-8,   
0,PC_TREMOLO_LEVEL,0x90,     
0,PC_TREMOLO_RATE,30, 
50,PC_NOTE_CUT,0,
0,PATCH_END  
};

const struct PatchStruct patches[] PROGMEM = {
{0,NULL,patch00,0,0},
{1,NULL,patch01,0,0},
{1,NULL,patch02,0,0},
{0,NULL,patch03,0,0},
{0,NULL,patch04,0,0}
};
