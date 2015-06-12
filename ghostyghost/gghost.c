/** \file gghost.c
*   \brief The main source file for the ghosty ghost project
*   \author kivan117 (James Elliott)
*   \date 2015
*/

#include <stdbool.h>
#include <avr/io.h>
#include <stdlib.h>
#include <avr/pgmspace.h>
#include <avr/interrupt.h>
#include <uzebox.h>

#include "data/title_tiles.inc" // menu tiles
#include "data/fonts_8x8.pic.inc" // the font we'll be using.
#include "data/dusk_city_tiles.inc" // tiles for dusk non-scrolling city tiles
#include "data/foreground_tiles.inc" // tiles for scrolling part of game graphics
#include "data/night_city_tiles.inc" // tiles for night time non-scrolling city tiles
#include "data/ghost_sprites.inc" // all the sprites for the game
#include "data/patches.inc" // sound effects
#include "data/gghost_title.inc" // main theme
#include "data/wave.inc" // contains a math lookup table for a sine function
#include "data/uzeboxlogo_8x8.pic.inc" // these are used to draw the normal uzebox logo
#include "data/uzeboxlogo_8x8.map.inc" // for the custom intro

uint_fast16_t     prng_state, ///< used to seed the pseudo random number generator
                  start_seed = 0; ///< tracks how long it takes the user to press start, which is used to seed the prng
uint_least16_t    lastbuttons=0, ///< saves the buttons pressed during the previous frame
                  joy=0, ///< bitfield used for tracking the buttons pressed during the current frame
                  pipe_x[4], ///< array of x values indicating the leading edge of an obstacle, used for collision detection
		          fake_x = 80; ///< variable for tracking the position of the player relative to upcoming obstacles, used for collision testing
uint_least8_t     city_offset = 0, ///< offset value used to start at the right tile for drawing the city. Used since the city can be drawn from 1 of 2 separate tile sets
                  brick_offset = 0, ///< tracks offset to the foreground tileset. Used since foreground tiles might be before or after the scrolling city and cloud tiles.
                  player_x = 80, ///< player x position on screen. 0  is far left
		          player_y = 40, ///< player y position on screen. 0 is top
		          gravity = 1, ///< amount gravity offsets player's vertical speed
		          jumpspeed = 7, ///< amount jumping offsets player's vertical speed
		          grav_tick = 3, ///< alarm value used for changing how often gravity is applied. Gives finer control of gravity.
		          maxfall = 4, ///< maximum vertical speed when falling
		          groundheight = 180, ///< y position, in pixels, used for detecting collision with the ground
		          ground_tiles = 25, ///< y position, in tiles, for detecting where the ground begins
                  pipe_width = 5, ///< horizontal width of obstacles
		          pipe_gap = 12, ///< vertical placement (in tiles) of the top of the opening in an obstacle
		          pipe_gap_width = 11, ///< vertical height (in tiles) of the opening in an obstacle
		          pipe_spacing = 8, ///< spacing (in tiles) between obstacles
		          pipe_alarm = 1, ///< alarm for placing the next obstacle
		          pipe_col_drawn = 0, ///< tracks how many vertical columns of tiles of the current obstacle has been drawn so far
		          pipe_y[4], ///< array that tracks the top of the opening in each column for collision detection
		          current_pipe=0, ///< used as the index in the pipe_x and pipe_y arrays for detecting collision with the correct obstacle
		          build_pipe =0, ///< used as the index in the pipe_x and pipe_y arrays to set information for the obstacle just built
		          pipe_x_offset = 144, ///< horizontal offset (in pixels) between ghost sprite and leading edge of an obstacle when it's first built off screen
		          pipe_color = 0, ///< used to randomly assign each obstacle a color (0 is blue, 1 is purple, 2 is red)
		          drawX = VRAM_TILES_H-1, ///< tracks x position in memory of the tile column to draw next. due to scrolling, position on screen and position in memory cannot be assumed to have any relationship
		          drawCityX = 0, ///< used to offset city tiles for parallax
		          current_frame=0, ///< tracks current frame of the sprite shown, used for animating the ghost
		          max_frames=3, ///< total frames in the ghost animation
		          frame_tick = 8, ///< alarm for updating the ghost animation
		          ghost_color = 0, ///< used to randomly assign ghost color on each new run. (0 is blue, 1 is red, 2 is purple)
		          save_block = 117, ///< the eeprom block id the high scores are saved to and read from
		          score = 0, ///< current player score
		          score_ones = 0, ///< ones digit of current player score, used for the floating score sprites
		          score_tens = 0, ///< tens digit of current player score, used for the floating score sprites
		          score_hundreds = 0, ///< hundreds digit of current player score, used for the floating score sprites
		          score_x = 108, ///< far left x position (in pixels) of the score sprites
		          topscores[10], ///< array of high scores, used to allow scores to be read and saved independent of game/menu flow
				  menu_x = 0, ///< x position (in tiles) of menu cursor
		          menu_y = 0, ///< y position (in tiles) of menu cursor
		          deathclock = 120, ///< alarm to move to high score screen 2 seconds after player loses
		          wave_tick = 15; ///< used as an index to traverse sine wave lookup table, provides smooth motion during custom intro
int_least8_t      yspeed = 0; ///< player's vertical speed (in pixels/frame)

unsigned char scroll=0; ///< tracks number of pixels scrolled since the last time a new column of tiles was drawn

bool scrollingOn=true, ///< tracks whether the screen has to be scrolled and also used to track if player is alive
	 mute = false; ///< tracks whether or not all audio should be muted


uint_least8_t bg[32]; ///< array used to track state of a column of tiles, either 0 for foreground or 1 for background. Needed for the parallax effect. Could be a 32 bit field but that's messier and I'm lazy.
const char * numbers[10] = {num0, num1, num2, num3, num4, num5, num6, num7, num8, num9}; ///< convenience array for displaying the floating score digit sprites
const char * player_sprites[9] = {ghost0, ghost1, ghost2, ghost3, ghost4, ghost5, ghost6, ghost7, ghost8}; ///< convenience array for displaying the ghost sprites
const char * current_sprite; ///< used as an index in player_sprites array to display correct ghost sprite

/**
 * \enum sky_state
 * \brief State of the background in game.
 */
typedef enum {DUSK, NIGHT} sky_state;
sky_state current_sky = NIGHT; ///< holds the actual current state of the bg in game to be drawn as night or dusk.

/**
 * \enum state
 * \brief Badly titled, but this is for the actual state of the game as a whole. Used for determining which screen to draw, what to do with player input, and what game logic to use.
 */
typedef enum {INTRO, MAIN_MENU, GAME, LOCAL_SCORES} state;
state game_state = INTRO; ///< Tracks current state of the game.

//these numbers are either tile indexes or they're offsets from a tile index
//for example, the first brick tile is tile 11 in the foreground tileset
//the "dark brick" through "right top corner" are offsets from this first brick, used for selecting brick style
//sky, grass, clouds, citytop, and citybottom are also offsets
//all the frame ones and the cursor are tile indexes
//normally you'd use 'maps' to draw things without all this but it worked out to be more convenient this way
//due to the odd scrolling nature and having to randomly generate different layouts
//the downside is updating the numbers when you add/remove tiles from the tileset

#define FIRST_BRICK 11 ///< offset from first foreground tile to first brick tile
#define DARK_BRICK 0 ///< offset from first brick to the darker background style bricks the ghost can fly in front of
#define LIGHT_BRICK 1 ///< offset from first brick to lighter colored bricks the ghost cannot pass through
#define LEFT_EDGE 2 ///< offset from first brick to the brick with stone edging used for the left wall of a column
#define RIGHT_EDGE 3 ///< offset from first brick to the brick with stone edging used for the right wall of a column
#define LEFT_BOTTOM_CORNER 4 ///< offset from first brick to the brick with stone edging on the left and bottom, used for top left corner of an opening through a column
#define RIGHT_BOTTOM_CORNER 5 ///< offset from first brick to the brick with stone edging on the right and bottom, used for top right corner of an opening through a column
#define BOTTOM_EDGE 6 ///< offset from first brick to the brick with a stone edge on the bottom, used for the upper edge of an opening
#define TOP_EDGE 7 ///< offset from first brick to the brick with a stone edge on the top, used for the lower edge of an opening
#define LEFT_TOP_CORNER 8 ///< offset from first brick to the brick with stone edging on the left and top, used for lower left corner of an opening through a column
#define RIGHT_TOP_CORNER 9 ///< offset from first brick to the brick with stone edging on the right and top, used for lower right corner of an opening through a column
#define SKY 0 ///< offset from start of foreground tiles to dark purple sky background tile
#define GRASS 1 ///< offset from start of foreground tiles to first grass tile with the highlight on top
#define CLOUDS 64 ///< offset from start of either scrolling city tileset to the first cloud tile
#define CITYTOP 0 ///<offset from the start of either scrolling city tileset to the first "upper half of the city skyline" tile
#define CITYBOTTOM 4 ///<offset from the start of either scrolling city tileset to the first "lower half of the city skyline" tile
#define BLACK 1 ///< offset from start of menu tiles to the solid black tile used as a background for the frame
#define FRAME_TL 2 ///< offset from start of menu tiles to the top left corner frame tile
#define FRAME_TR 3 ///< offset from start of menu tiles to the top right corner frame tile
#define FRAME_BL 4 ///< offset from start of menu tiles to the bottom left corner frame tile
#define FRAME_BR 5 ///< offset from start of menu tiles to the bottom right corner frame tile
#define FRAME_T 6 ///< offset from start of menu tiles to the top edge frame tile
#define FRAME_B 7 ///< offset from start of menu tiles to the bottom edge frame tile
#define FRAME_L 8 ///< offset from start of menu tiles to the left edge frame tile
#define FRAME_R 9 ///< offset from start of menu tiles to the right edge frame tile
#define CURSOR 10 ///< offset from start of menu tiles to the cursor tile
#define UPCURSOR 11 ///< offset from start of menu tiles to the cursor tile

void processMainMenu(void);
void processLocalHighScoreMenu(void);
void drawIntro(void);
void processIntro(void);
void initIntro(void);
void processControls(void);
void processPlayerMotion(void);
void processSprites(void);
void processScrollSpeed(void);
void loadNextStripe(void);
static void initialSetup(void);
static void gameSetup(void);
void drawFrame(void);
void drawMainMenu(void);
void refreshMainMenuSound(void);
void drawLocalHighScoreMenu(void);
void drawMenuCursor(bool up);
void eraseMenuCursor(void);
void Save(u8 hiscore);
void LoadScore(u8 index0, u8 index1);
void plusScore(void);
u8 checkEeprom(void);
void wipeEeprom(void);
void updateCity(void);
uint_fast16_t prng(void);
void seedprng(uint_fast16_t seed);
uint_fast8_t fakemod(uint_fast8_t num1, uint_fast8_t num2);
void setBGTiles(sky_state bg_state);
void randomSky(void);

/**
 * \brief The main game loop. This just cycles endlessly, it uses the game's 'state' to determine which screen to show and what to do.
 */
int main(){
	//looping back and forth forever (cards against humanity reference)
	while(1)
	{


		//some basic prep work performed once before our custom intro
		if(game_state == INTRO)
		{
			initialSetup();
			initIntro();
		}
		//perform custom intro
		while(game_state == INTRO)
		{
			//wait until the next frame
			WaitVsync(1);
			drawIntro();
			processIntro();
		}
		//prep the main menu
		if(game_state == MAIN_MENU)
		{
			FadeOut(0,true);
			ClearVram();
			SetTileTable(title_tiles);
			SetFontTilesIndex(TITLE_TILES_SIZE);
			drawMainMenu();
			FadeIn(0,false);
		}
		//draw menu and handle input
		while(game_state == MAIN_MENU)
		{
			WaitVsync(1);
			drawMenuCursor(false);
			processMainMenu();
		}
		if(game_state== GAME)
		{
			//run our setup for the main game
			ClearVram();
			FadeOut(0,true);
			gameSetup();
			FadeIn(0,false);
		}
		//when we're in the gameplay portion, draw and accept input for the game
		while(game_state == GAME)
		{
			WaitVsync(1);
			processScrollSpeed(); //scrolls screen as appropriate
			updateCity(); //offsets city for parallax
			processControls(); //accepts and processes controller input
			processPlayerMotion(); //update player position
			processSprites(); //updates and moves player image to player position
		}
		if(game_state == LOCAL_SCORES)
		{
			FadeOut(0,true);
			SetTileTable(title_tiles);
			SetFontTilesIndex(TITLE_TILES_SIZE);
			drawLocalHighScoreMenu(); //draw up the high score screen
			FadeIn(0,false);
			deathclock=120; //reset death timer to 2 seconds
			if(score > topscores[9])
			{
			    LoadScore(0, 9); //load top 10 saved high scores
			    Save(score); //save our current score if it's high enough
			    score = 0;
			    drawLocalHighScoreMenu(); //draw up the high score screen
			}
		}
		//draw and accepts input for the local high score screen
		while(game_state == LOCAL_SCORES)
		{
			WaitVsync(1);
			processLocalHighScoreMenu();
		}
    }
}

/**
 * \brief Performs some basic initialization functions.
 *
 * Sets up our graphics, initializes a few variables for convenience, loads saved scores and gets the music going.
 */
static void initialSetup()
{
	SetSpritesTileTable(ghost_sprites); //sets the tiles to be used for our various sprites
	SetFontTilesIndex(TITLE_TILES_SIZE); //tiles for the font were included immediately after the include for background tiles
	                               //therefore this says how many tiles in memory to move forward from the first one
	                               //in order to find the beginning of the font tiles
	SetTileTable(title_tiles); //sets the tiles to be used for the normal background tiles in the game
	                     //fonts use this and the index above to set font tiles
	InitMusicPlayer(patches); //initialize the sound engine
	SetMasterVolume(0xff); //set volume to max
	StartSong(midisong); //start playing the main theme
	ClearVram(); //fill entire screen with first tile in the tileset (blank the screen)

	//checks if our desired eeprom block is setup correctly,
	//if not, it wipes it so we don't have to deal with garbage data in the high score list
	if(checkEeprom()==1)
	{
		wipeEeprom();
	}
	//load our top 10 saved scores from eeprom
	LoadScore(0, 9);
}

/**
 * \brief Processes controller input for the main menu.
 */
void processMainMenu(void)
{
	//read in our player one joypad input
	joy=ReadJoypad(0);

	//pressing something and it isn't the same buttons as last frame so it's a new button press, not a hold
	if(joy!=lastbuttons)
	{
		//if player 1 is currently pressing start
		if(joy&BTN_START)
		{
			//if player cursor is at top menu choice, which is 'start game'
			if(menu_y == 15)
			{
				seedprng(start_seed);
				//switch our game state to game, which pops us out of the main menu and into the game (refer to main function)
				game_state = GAME;
			}
			//if cursor is on second option, which is 'hi scores'
			else if(menu_y == 17)
			{
				seedprng(start_seed);
				//switch our game state to high scores, which pops us out of the main menu and into the high scores menu (refer to main function)
				game_state = LOCAL_SCORES;
			}
		}
		if(joy&BTN_UP) //player pressed up
		{
			if(menu_y > 15) //if we're not at the top menu option
			{
				eraseMenuCursor(); //erase the old cursor position
				menu_y -= 2; //move cursor up one option
			}
		}
		else if (joy&BTN_DOWN) //player pressed down
		{
			if(menu_y < 19) //if we're above the bottom option
			{
				eraseMenuCursor(); //erase cursor at old position
				menu_y += 2; //move cursor down one option
			}
		}
		else if ((joy&BTN_LEFT) || (joy&BTN_RIGHT)) //player pressed left or right on d-pad
		{
			if(menu_y == 19) //if we're on the third menu option, which is sound on/off
			{
				if(mute) //if game is muted, unmute it
				{
					SetMasterVolume(0xff);
					mute=false;
				}
				else //if game is not muted, mute it
				{
					SetMasterVolume(0x00);
					mute=true;
				}
				refreshMainMenuSound(); //update menu screen to show music as on/off now that it changed
			}
		}
	}

	lastbuttons=joy; //track which buttons were pressed this frame for comparison next frame
	start_seed++;
}

/**
 * \brief Performs setup and re-initialization needed before each new game.
 *
 * Resets the player score, resets variables for drawing columns, sets a new random ghost color, moves the player back to the starting position, erases columns from last game,
 * turns scrolling back on and makes the player visible again.
 */
static void gameSetup()
{
	randomSky();
	//fill screen with tile 1 again to erase menu
	ClearVram();

	for(u8 i = 0; i < 4; i++) //reset column data with 0's to start fresh
	{
		pipe_x[i] = 0;
		pipe_y[i] = 0;
	}
	for(u8 k = 0; k < 32; k++)
	{
		bg[k] = 1;
	}

	//reset all score data from last game to 0
	score = 0;//score = 0;
	score_ones=0;
	score_tens=0;
	score_hundreds=0;

	fake_x = 80; //reset how far we've flown
	player_x = 80; //reset player position
	player_y = 40;
	yspeed = 0; //make sure we start at 0 speed

	//draw the background
	for(u8 i = 0; i < VRAM_TILES_H; i++)
	{
		pipe_alarm=2; //make sure we never draw a column while we're drawing the starting screen
		loadNextStripe(); //go through each column and draw the background
	}

	//select a random color for the ghost and set the appropriate sprite
	ghost_color=(prng()%3); //the ghost has 3 frames and 3 color options, so we set the active sprite to the frame count (0 - 2) + the color (0, 3, or 6) to get the correct sprite
	ghost_color=(ghost_color+(ghost_color<<1));
	current_sprite = player_sprites[current_frame+ghost_color];
	//assign and move the player image to start the new game
	MoveSprite(0,player_x,player_y,3,3);
	MapSprite2(0,current_sprite,0);
	//make player visible
	SetSpriteVisibility(true);

	//reset variables to draw new columns correctly
	current_pipe=0;
	build_pipe=0;
	pipe_alarm = 1;
	pipe_col_drawn = 0;

	//turn scrolling on to begin the game
	scrollingOn=true;

}

/**
 * \brief Handles input for gameplay. Reads player 1 joypad and processes input for the main game.
 */
void processControls(void){
	//read current player 1 input, save in joy variable
	joy=ReadJoypad(0);

	if(joy) //if any button at is is being pressed
	{
		if(scrollingOn) //if we're scrolling the screen (player is alive)
		{
			if(lastbuttons!=joy) //if we're pressing a new button, not holding one
			{
				yspeed = -jumpspeed; //make player jump up
				TriggerFx(4,0x88,true);//play our bouncing sound effects
				TriggerFx(5,0x88,true);
				grav_tick=1; //reset gravity ticks. doing this ensures that no matter where the gravity timer was, we always get a consistent jump height
			}
		}
		else if(joy&BTN_START) //if player is dead and start was pressed
		{
			if(deathclock<105)
			{
				game_state = LOCAL_SCORES; //exit main game state, enter high score screen state (refer to main function)
			}
		}

		if(joy&BTN_SELECT)//alive or note, if select was pressed...
		{
			if(lastbuttons!=joy) //if it was JUST pressed and not held
			{
				if(mute) //if volume is muted, unmute it
				{
					SetMasterVolume(0xff);
					mute=false;
					ResumeSong();
				}
				else //if volume is normal, mute it
				{
					StopSong();
					SetMasterVolume(0x00);
					mute=true;
				}
			}

		}
	}

	//save current input as lastbuttons so we can check if new buttons are pressed next time
	lastbuttons=joy;
}

/**
 * \brief Handles screen scrolling.
 */
void processScrollSpeed(void)
{

	if(scrollingOn)
	{
		Scroll(1,0); //scroll background tiles left 1 pixel horizontally and 0 vertically
		scroll++; //track how far we've scrolled the background since loading a new column of tiles
		fake_x++; //track how far player has flown since start of game, used for column collision checking

		//if we've scrolled at least one whole tile since loading a new column of tiles
		if(scroll>=8){
			loadNextStripe(); //load a new column of background tiles to the far right off screen
			scroll=0; //reset pixels scrolled since we last loaded new tiles
		}
	}

}

/**
 * \brief Draws vertical columns of background tiles.
 *
 * Draws the nonmoving background tiles except for the clouds and city, and draws the obstacle columns.
 * Also tracks which columns are foreground (columns) and which are background (city and clouds) for the parallax effect to work properly.
 */
void loadNextStripe(void)
{
	drawX++; //move right one column of tiles
	if(drawX >= 32) //if destination column is greater than number of tile columns, go back to 0
		drawX=0;
	drawCityX++; //this counter is used for the parallax effect of the city. wraps at 4 because the city is 4 tiles wide
	if(drawCityX >= 4)
		drawCityX = 0;

	if(pipe_col_drawn == 0) //if we're not drawing an obstacle column, count down until the next one
	    pipe_alarm--;

	if(pipe_alarm == 0) //alarm to draw new obstacle triggered
	{
		bg[drawX] = 0;
		pipe_col_drawn++; //track how much of the obstacle we've drawn horizontally
	    if(pipe_col_drawn == 1) //if this is the far left part of the obstacle...
	    {
	    	pipe_x[build_pipe] = fake_x+pipe_x_offset; //set our collision checking data
	    	pipe_y[build_pipe] = pipe_gap<<3;
	    	build_pipe++; //advance one in our arrays that track collision data, reset to 0 if we're above 4 (max 3 should be on screen at once so 4 are tracked at once to avoid errors)
	    	if(build_pipe > 3)
	    		build_pipe = 0;
			for(u8 y=0; y < SCREEN_TILES_V; y++) //draw the vertical stripe of tiles
			{
				if(y == pipe_gap-1) //draw foreground bricks
				{
					SetTile(drawX, y, brick_offset+FIRST_BRICK+LEFT_TOP_CORNER+(pipe_color*10));
				}
				else if(y == pipe_gap+pipe_gap_width+1) //draw foreground bricks
				{
					SetTile(drawX, y, brick_offset+FIRST_BRICK+LEFT_BOTTOM_CORNER+(pipe_color*10));
				}
				else if(y < pipe_gap || y > pipe_gap+pipe_gap_width) //draw foreground bricks
				{
					SetTile(drawX, y, brick_offset+FIRST_BRICK+LEFT_EDGE+(pipe_color*10));
				}
				else //draw background bricks
				{
					SetTile(drawX, y, brick_offset+FIRST_BRICK+DARK_BRICK+(pipe_color*10));
				}
			}
	    }
	    else if(pipe_col_drawn <= (pipe_width-1)) //if we're not at the far left or right of an obstacle column, but we're drawing the middle of it
		{
			//draw pipe column
			for(u8 y=0; y < SCREEN_TILES_V; y++)
			{
				if(y == pipe_gap-1) //draw foreground bricks
				{
					SetTile(drawX, y, brick_offset+FIRST_BRICK+TOP_EDGE+(pipe_color*10));
				}
				else if(y == pipe_gap+pipe_gap_width+1) //draw foreground bricks
				{
					SetTile(drawX, y, brick_offset+FIRST_BRICK+BOTTOM_EDGE+(pipe_color*10));
				}
				else if(y < pipe_gap || y > pipe_gap+pipe_gap_width) //draw foreground bricks
				{
					SetTile(drawX, y, brick_offset+FIRST_BRICK+LIGHT_BRICK+(pipe_color*10));
				}
				else //draw background bricks
				{
					SetTile(drawX, y, brick_offset+FIRST_BRICK+DARK_BRICK+(pipe_color*10));
				}
			}

		}
	    else if(pipe_col_drawn <= (pipe_width)) //if we're drawing the far right part of an obstacle column
		{
			//draw pipe column
			for(u8 y=0; y < SCREEN_TILES_V; y++)
			{
				if(y == pipe_gap-1) //draw foreground bricks
				{
					SetTile(drawX, y, brick_offset+FIRST_BRICK+RIGHT_TOP_CORNER+(pipe_color*10));
				}
				else if(y == pipe_gap+pipe_gap_width+1) //draw foreground bricks
				{
					SetTile(drawX, y, brick_offset+FIRST_BRICK+RIGHT_BOTTOM_CORNER+(pipe_color*10));
				}
				else if(y < pipe_gap || y > pipe_gap+pipe_gap_width) //draw foreground bricks
				{
					SetTile(drawX, y, brick_offset+FIRST_BRICK+RIGHT_EDGE+(pipe_color*10));
				}
				else //draw background bricks
				{
					SetTile(drawX, y, brick_offset+FIRST_BRICK+DARK_BRICK+(pipe_color*10));
				}
			}

		}
		else //we're past the allowed width for drawing the obstacle, stop drawing the obstacle and reset variables
		{
			bg[drawX] = 1;
			pipe_col_drawn = 0; //reset how much of the column we've drawn
			pipe_alarm = pipe_spacing; //reset the alarm to begin drawing a new obstacle
			pipe_gap = 2+(prng()%12); //randomly set where the vertical opening will be
			pipe_color = prng()%3; //randomly set the color of the next one
		}
	}
	else //not drawing an obstacle column, so just draw normal background tiles
	{
		bg[drawX] = 1;
		for(u8 y=0; y < SCREEN_TILES_V; y++)
		{
			if(y<ground_tiles-3) //above a certain point, draw generic sky
			{
				if(current_sky == DUSK) //currently set to draw the sunset background, so set sky tiles to sunset
				{
					if(y>13)
						SetTile(drawX, y, brick_offset+SKY+(y-11));
					else
						SetTile(drawX, y, brick_offset+SKY);
				}
				else //currently set to draw the night background, so set all sky tiles to night
					SetTile(drawX, y, brick_offset+SKY);
			}
			else if(y==ground_tiles) //at ground level, draw the top and bottom of the grass layer. They're separate tiles because the top has a little highlight to make it look flat
				SetTile(drawX, y, brick_offset+GRASS);
			else
				SetTile(drawX, y, brick_offset+GRASS+1);
		}
	}
}

/**
 * \brief Updates the player position and carries out collision checking. Most of the game logic is in this function.
 */
void processPlayerMotion(void){

	//update player position
	if(--grav_tick==0) //decrement gravity alarm, if it's at 0, enact gravity and reset the alarm
	{
		yspeed+=gravity;
	    grav_tick = 3;
	}
	if(yspeed > maxfall) //if after applying gravity we're beyond our max fall rate, change to max fall rate
	{
		yspeed = maxfall;
	}

	if(player_y + yspeed < 0) //don't go above the top of the screen
	    player_y = 0;
	else if(player_y+yspeed > groundheight) //don't fall below ground level
	{
			player_y = groundheight;
			yspeed = 0;
	}
	else
		player_y += yspeed; //in all other cases, just adjust player's y position according to current vertical speed

	//check collisions
	if(player_y >= groundheight) //if we're at or below the ground level
	{
		if(scrollingOn) //if we're currently alive
		{
			TriggerFx(3,0x7f,true); //play collision sound
		    scrollingOn = false; //turn off scrolling (stop being alive)
		}
	}
	if(fake_x == pipe_x[current_pipe]) //if the front of the ghost is exactly equal with the front of the next obstacle column
	{
		if(player_y > pipe_y[current_pipe] && player_y < pipe_y[current_pipe]+((pipe_gap_width-1)<<3)) //if we're in the opening and not smacking into the column...
		{
			plusScore(); //add to our score
		}
	}
	else if(fake_x > (pipe_x[current_pipe]+((pipe_width+2)<<3)))// if we're entirely past the current obstacle column
	{
		current_pipe++; //start checking the next one instead
		if(current_pipe > 3)
		{
			current_pipe = 0;
		}
	}
	else if(fake_x > pipe_x[current_pipe] && fake_x < (pipe_x[current_pipe]+((pipe_width+2)<<3))) //if we're in the middle of a column horizontally
	{
		if(player_y < pipe_y[current_pipe] || player_y > pipe_y[current_pipe]+((pipe_gap_width-1)<<3)) //AND we are above or below the opening in it
		{
			if(scrollingOn) //if we're still alive, play collision sound and stop being alive
			{
				TriggerFx(3,0x7f,true);
				scrollingOn = false;
			}
			yspeed=0; //stops us vertically (and accidentally creates a cool megaman friction-y sliding effect through the column)
		}
	}

	if(!scrollingOn) //if player is dead, count down 2 seconds and go to high score screen
	{
		deathclock--;
		if(deathclock==0) //it's been 120 frames (2 seconds) since player died
		{
			game_state = LOCAL_SCORES; //switch out of main game state to high score screen state (see main function)
		}
	}

}

/**
 * \brief Animates and moves player sprite, and updates and centers score sprites.
 */
void processSprites(void){

	//update player sprite
	if(scrollingOn) //if player is alive, decrement animation alarm
	{
		frame_tick--;
	}

	if(frame_tick == 0) //animation alarm has been reached, reset alarm and change sprite to next frame
	{
		frame_tick = 8; //reset alarm
		current_frame++; //move forward to next animation frame
		if(current_frame == max_frames)
		{
			current_frame=0;
		}
		current_sprite = player_sprites[current_frame+ghost_color]; //change our tracking variable to the correct sprite based on new frame and current color
		MapSprite2(0, current_sprite, 0); //actually reassign the sprites in memory to the correct images
	}
	//move player sprite to player position
	MoveSprite(0,player_x,player_y,3,3);

	//map score sprites and move score to correct place
	MapSprite2(9, numbers[score_ones],0); //assign ones place sprite and center it according to player score
	MoveSprite(9,score_x, 8,1,2);
	if(score_tens!=0) //if player score high enough to have tens digit, assign that sprite and move stuff over to recenter
	{
		MapSprite2(11, numbers[score_tens],0);
		MoveSprite(11,score_x, 8, 1, 2);
		MoveSprite(9,score_x+8, 8, 1, 2);
	}
	else //score is below 10, so move tens digit off screen (solves bug where old tens place digit from last game was in the way)
	{
		MoveSprite(11,SCREEN_TILES_H << 3, 8, 1, 2);
	}
	if(score_hundreds!=0) //score is somehow > 100, assign 100's place digit sprite and recenter score
	{
		MapSprite2(13, numbers[score_hundreds],0);
		MoveSprite(13,score_x, 8, 1, 2);
		MoveSprite(11,score_x+8, 8, 1, 2);
		MoveSprite(9,score_x+16, 8, 1, 2);
	}
	else //score is < 100, move 100's place digit sprite off screen for the same reason as the ten's digit above
	{
		MoveSprite(13,SCREEN_TILES_H << 3, 8, 1, 2);
	}
}

/**
 * \brief Loads saved scores from eeprom.
 *
 * Loads scores from eeprom and saves them into current game memory for use.
 * \param index0 Lower boundary score to load (inclusive)
 * \param index1 Upper boundary score to load (inclusive)
 */
void LoadScore(u8 index0, u8 index1)
{
	if(index1 > 9)
		index1 = 9;
	//Initialize a struct and define the block id
	struct EepromBlockStruct ebs; //create a temporary eeprom block struct
	ebs.id = save_block; //set it to read this game's block
	if(EepromReadBlock(ebs.id, &ebs)==0) //read data from eeprom into the struct, if it works, proceed
	{
		for(u8 i = index0; i<=index1; i++) //read scores from index0 to index1 and save them into our top score array for use
		    topscores[i]=(u8)ebs.data[i];
	}
}

/**
 * \brief Accepts a numerical score, saves it to eeprom if it's high enough.
 * \param hiscore the value to compare and possibly save to eeprom
 */
void Save(u8 hiscore)
{
	struct EepromBlockStruct ebs; //create a temporary eeprom block struct for use
	ebs.id = save_block; //assign it to this game's eeprom block number

	//compare input score to topscores array, if input score is high enough, insert the score in the correct position
	//initially had some problems getting searching and sorting to work with scores.
	//it wasn't actually at all related to this function though, it was a problem elsewhere. need to refactor this to just use a for loop like it was before.
	u8 index = 0;
	bool searching=true;
	while(searching)
	{
		if(index > 9)
			searching=false;
		if(topscores[index] < hiscore)
		{
			for(u8 k = 9; k > index; k--)
			{
				topscores[k] = topscores[k-1];
			}
			topscores[index]=hiscore;
			searching=false;
		}
		index++;
	}

	//topscores array accurately reflects our top 10, so assign them to the temp eeprom block struct
	for(u8 h = 0; h < 10; h++)
	{
		ebs.data[h] = topscores[h];
	}

	ebs.data[17] = 0x17; //THIS IS KEY, we check this value to make sure the block is formatted correctly whenever the game is initially booted up

	EepromWriteBlock(&ebs); //actually write the data to eeprom
}

/**
 * \brief Helper function to draw the reusable menu frame.
 */
void drawFrame(void)
{
	SetSpriteVisibility(false); //turn off sprites for now, the menus only use background tiles anyway

	//to minimize weird problems with drawing a static screen due to mode 3 scrolling, or VRAM_TIES_H vs SCREEN_TILES_H (or something, couldn't figure it out)
	//scroll the game back to its starting position then turn scrolling back off
	scrollingOn=true;
	while(scroll != 0) //reset to align edge of screen to a tile, not part way in between
	{
		processScrollSpeed();
	}
	while(drawX != (VRAM_TILES_H-1)) //scroll until the screen is aligned with its starting position (tile position 0 at far left)
	{
		processScrollSpeed();
	}
	scrollingOn=false;


	ClearVram(); //clear screen to prep for drawing the frame

	u8 drawXTemp = fakemod((drawX+2),VRAM_TILES_H);//variable used for tracking horizontal position of tiles as we draw them. drawing is done top to bottom left to right

	SetTile(drawXTemp, 1, FRAME_TL); //place top left corner tile
	for(u8 y=2; y<SCREEN_TILES_V-2; y++)//draw lefthand border
	{
		SetTile(drawXTemp, y, FRAME_L);
	}
	SetTile(drawXTemp, SCREEN_TILES_V-2, FRAME_BL); //place bottom left corner tile

	for(u8 x=0; x<24; x++)//draw middle portion of frame until we reach the right hand side
	{
		drawXTemp=fakemod((drawXTemp+1),VRAM_TILES_H);
		SetTile(drawXTemp, 1, FRAME_T); //draw top piece
		for(u8 y=2; y<SCREEN_TILES_V-2; y++) //fill middle with black
		{
			SetTile(drawXTemp, y, BLACK);
		}
		SetTile(drawXTemp, SCREEN_TILES_V-2, FRAME_B); //draw bottom piece
	}

	drawXTemp=fakemod((drawXTemp+1),VRAM_TILES_H);
	SetTile(drawXTemp, 1, FRAME_TR); //place top right corner tile
	for(u8 y=2; y<SCREEN_TILES_V-2; y++) //draw righthand border
	{
		SetTile(drawXTemp, y, FRAME_R);
	}
	SetTile(drawXTemp, SCREEN_TILES_V-2, FRAME_BR); //place bottom right corner tile

}

/**
 * \brief Increments player score and updates individual pieces used for score sprites.
 *
 * The ones, tens, and hundreds digit are tracked separately for the floating score sprite shown in game, so in addition to updating the normal score variable, this function correctly updates those as well.
 * This method was chosen since while it takes more ram, it's easy.
 */
void plusScore(void)
{
	score++; //increment actual score variable

	score_ones++; //increment ones digit every time
	if(score_ones > 9) //if necessary, increment tens digit and reset ones digit
	{
		score_ones=0;
		if(score_tens==0)
			score_x-=4; //recenter score sprites
		score_tens++;
	}
	if(score_tens > 9) //if player somehow reaches a high enough score, increment hundreds digit, reset tens digit
	{
		score_tens=0;
		if(score_hundreds==0)
			score_x-=4; //recenter score sprites
		score_hundreds++;
	}
}

/**
 * \brief Draws Main Menu screen.
 */
void drawMainMenu()
{
	//setup cursor position for use with this menu screen
	menu_x = fakemod((drawX+9),VRAM_TILES_H);
	menu_y = 15;
	ClearVram(); //wipe screen
	drawFrame(); //draw up generic menu frame

	//draw fancy title. broken into pieces so it can be reused as much as possible to save space
	DrawMap(fakemod((drawX+7),VRAM_TILES_H),4,title_gh);
	DrawMap(fakemod((drawX+13),VRAM_TILES_H),4,title_o);
	DrawMap(fakemod((drawX+16),VRAM_TILES_H),4,title_st);
	DrawMap(fakemod((drawX+21),VRAM_TILES_H),4,title_y);
	DrawMap(fakemod((drawX+9),VRAM_TILES_H),9,title_gh);
	DrawMap(fakemod((drawX+15),VRAM_TILES_H),10,title_moon);
	DrawMap(fakemod((drawX+18),VRAM_TILES_H),9,title_st);

	//draw menu options
	Print(fakemod((drawX+11),VRAM_TILES_H),15,PSTR("START GAME"));
	Print(fakemod((drawX+11),VRAM_TILES_H),17,PSTR("HI SCORES"));
	Print(fakemod((drawX+11),VRAM_TILES_H),19,PSTR("SOUND:"));
	//draw copyright info
	Print(fakemod((drawX+4),VRAM_TILES_H),24,PSTR("(C) 2015 JAMES ELLIOTT"));
	//draw on/off next to sound option
	refreshMainMenuSound();
}

/**
 * \brief Draws local high score menu.
 *
 * Uses the values saved in the topscores array, not eeprom values, this allows displaying scores separately from saving/loading.
 */
void drawLocalHighScoreMenu(void)
{
	//set cursor for use with this menu (may one day be needed for scrolling)
	menu_x = fakemod((drawX+9),VRAM_TILES_H);
	menu_y = 15;
	ClearVram(); //blank screen
	drawFrame(); //draw generic gui frame
	Print(fakemod((drawX+8),VRAM_TILES_H),3,PSTR("LOCAL HI SCORES")); //write menu title at top of screen

	for(u8 i = 0; i < 10; i++) //print scores 1 - 10 from topscores array
	{
		PrintInt(fakemod((drawX+17),VRAM_TILES_H),6+(i<<1),topscores[i], false);
		PrintInt(fakemod((drawX+11),VRAM_TILES_H),6+(i<<1),i+1, false);
		Print(fakemod((drawX+12),VRAM_TILES_H),6+(i<<1),PSTR("."));
	}
}

/**
 * \brief Helper function to draw cursor for menus.
 */
void drawMenuCursor(bool up)
{
	if(up)
	{
		SetTile(menu_x,menu_y, UPCURSOR);
	}
	else
		SetTile(menu_x,menu_y, CURSOR);
}

/**
 * \brief Helper function to erase cursor on menus.
 */
void eraseMenuCursor()
{
	SetTile(menu_x, menu_y, BLACK);
}

/**
 * \brief Helper function to update sound "on/off" on main menu.
 */
void refreshMainMenuSound()
{
	if(mute)
		Print(fakemod((drawX+18),VRAM_TILES_H),19,PSTR("OFF"));
	else
		Print(fakemod((drawX+18),VRAM_TILES_H),19,PSTR("ON "));
}

/**
 * \brief Processes controller input during local high score menu.
 */
void processLocalHighScoreMenu(void)
{
	//read in our player one joypad input
	joy=ReadJoypad(0);

	//if player 1 is currently pressing start
	if(joy != lastbuttons)
	{
		if((joy&BTN_START))
		{
			//switch our game state to game, which pops us out of the main menu and into the game (refer to main function)
			game_state = GAME;
		}
	}
	lastbuttons=joy;
}

/**
 * \brief Used to setup the game's eeprom block on first run to prevent garbage data. Checks for a magic number to verify formatting.
 *
 * \return 0 if block is formatted correctly for this game, 1 if not.
 */
u8 checkEeprom(void)
{
	struct EepromBlockStruct ebs; //create temp eeprom block struct for use
	ebs.id = save_block; //assign to this game's block id
	if(EepromReadBlock(ebs.id, &ebs)==0) //reads block values into temp struct, if successful, moves on
	{
		if(ebs.data[17] == 0x17) //looks for magic number
			return 0; //block was read, and magic number was present, block is good
	}
	return 1; //something failed along the way, block is bad
}

/**
 * \brief Blanks this game's eeprom slot.
 *
 * Used on first run to avoid garbage data in high score list. Could be used to intentionally wipe scores too, but isn't right now.
 */
void wipeEeprom(void)
{
	struct EepromBlockStruct ebs;//create temp eeprom block struct for use
	ebs.id = save_block; //assign temp struct to this game's eeprom block id

	for(u8 i = 0; i < 17; i++) //cycle through all 30 data bytes and set them to 0
		ebs.data[i] = 0x00;

	ebs.data[18] = 'D';
	ebs.data[19] = 'E';
	ebs.data[20] = 'F';
	ebs.data[21] = 'A';
	ebs.data[22] = 'U';
	ebs.data[23] = 'L';
	ebs.data[24] = 'T';
	ebs.data[25] = ' ';


	ebs.data[17] = 0x17; //set magic number so the block will check out as being good in the future
	EepromWriteBlock(&ebs); //write to eeprom
}

/**
 * \brief Setup for custom intro
 */
void initIntro(void)
{
	StopSong(); //don't play song during intro
	MapSprite2(0, player_sprites[0], 0); //setup blue ghost for drawing
	player_x = 0; //set ghost to far left
	player_y = 80; //center ghost vertically
	SetTileTable(logo_tileset); //setup tiles for drawing uzebox logo
}

/**
 * \brief Draws the custom intro
 */
void drawIntro(void)
{
	ClearVram(); //wipe screen each frame
	frame_tick--;
	if(frame_tick == 0) //animation alarm has been reached, reset alarm and change sprite to next frame
	{
		frame_tick = 8; //reset alarm
		current_frame++; //move forward to next animation frame
		if(current_frame == max_frames)
		{
			current_frame=0;
		}
		current_sprite = player_sprites[current_frame]; //change our tracking variable to the correct sprite based on new frame
		MapSprite2(0, current_sprite, 0); //actually reassign the sprites in memory to the correct images
	}
	MoveSprite(0, player_x, player_y, 3, 3); //position ghost sprite
	DrawMap(13,12,map_uzeboxlogo); //draw uzebox logo and name
    if((player_x > 104)&&(player_x<108)) //at the right moment, draw the shiny reflection on the logo
        DrawMap(13,12,map_uzeboxlogo2);
}

/**
 * \brief Logic for custom intro and processes controller input for skipping intro.
 */
void processIntro(void)
{
	//cycles through our sine function to move the ghost smoothly
	wave_tick++;
	if(wave_tick > 127)
		wave_tick = 0;
	player_y = (u8)(100+pgm_read_byte(&(sine32[wave_tick]))); //set ghost height based on sine function
	player_x++; //move ghost left to right 1 pixel
	if(player_x == 104) //at correct moment, trigger sound effect
		TriggerFx(13,0x88,true);
	if(player_x > 224) //when ghost is off screen, end intro and move to main menu
	{
		ResumeSong();
		SetTileTable(title_tiles);
		frame_tick = 8;
		current_frame = 0;
		game_state = MAIN_MENU;
	}

	//read in our player one joypad input
	joy=ReadJoypad(0);

	//if player 1 is currently pressing start
	if((joy&BTN_START) && (joy != lastbuttons))
	{
		ResumeSong();
		SetTileTable(title_tiles);
		frame_tick = 8;
		current_frame = 0;
		lastbuttons=joy;
		game_state = MAIN_MENU;
	}
	lastbuttons=joy;
}

/**
 * \brief Redraw the background clouds and city, adjusting to offset scrolling and produce a still image
 *
 * The stationary city and clouds are produced by cycling through a set of cloud and city tiles, sequentially offset
 * one pixel to the right to negate the effect of all tiles being drawn one pixel to the left as the screen scrolls.
 * This function is pretty clock-heavy and could possibly use further optimization but I don't know how to do much more.
 */
void updateCity(void)
{
	//if the screen isn't moving, there's no reason to change the cloud and city tiles
	if(!scrollingOn)
		return;

	//some convenience variables. faster to calculate once and set a variable for reuse
	uint_fast8_t x_scroll4, x_scroll8, x_draw;
	x_scroll4 = scroll<<2;
	x_scroll8 = x_scroll4<<1;

	//cycle through all 32 horizontal positions in vram and set the correct city and cloud tiles in each column
	for(u8 x = 0; x < 32; x++)
	{
		if(bg[x])
		{
			x_draw = (x-drawCityX)&3;
			SetTile(x, ground_tiles-3, city_offset+CLOUDS+(x_draw)+(x_scroll4));
			SetTile(x, ground_tiles-2, city_offset+CITYTOP+(x_draw)+(x_scroll8));
			SetTile(x, ground_tiles-1, city_offset+CITYBOTTOM+(x_draw)+(x_scroll8));
		}
	}
}

/**
 * \brief Set seed used by the pseudo-random number generator.
 * \param seed value to set the seed to
 */
void seedprng(uint_fast16_t seed){
    prng_state = seed;
}

/**
 * \brief A pseudo-random number generator provided by D3thAdd3r (Lee Weber)
 *
 * Used in place of rand() for speed considerations. Produces reliably "random" output and accepts a seed value. \n
 * taps: 16 14 13 11; feedback polynomial: x^16 + x^14 + x^13 + x^11 + 1
 */
uint_fast16_t prng(void){
    uint_fast16_t bit = ((prng_state >> 0) ^ (prng_state >> 2) ^ (prng_state >> 3) ^ (prng_state >> 5) ) & 1;
    prng_state = (prng_state >> 1) | (bit << 15);
    return prng_state;
}

/**
 * \brief Compares two numbers, outputs the first mod the second
 *
 * Not a true mod function, used because real mod function requires division and is slow. Only compares the two numbers,
 * subtracts the second from the first until the output is below the value of the second. Should be used when the first value is known to be less than 2 times the second.
 *
 * \param num1 potentially higher value to be mod by the second
 * \param num2 the number to limit the output below
 *
 */
uint_fast8_t fakemod(uint_fast8_t num1, uint_fast8_t num2)
{
	while(num1>=num2)
	{
		num1-=num2;
	}
	return num1;
	//return num1 >= num2 ? (num1-num2) : num1;
}

/**
 * \brief Accepts a sky_state and sets the correct tile set and tile offsets for use
 * \param bg_state the sky_state to act on
 *
 */
void setBGTiles(sky_state bg_state)
{
	if(bg_state == DUSK)
	{
		//set tileset to dusk city tiles, set city offset to 0, set brick offset to 96
		brick_offset = DUSK_CITY_TILES_SIZE;
		city_offset = 0;
		SetTileTable(dusk_city_tiles);
	}
	else if (bg_state == NIGHT)
	{
		//set tileset to bricks, set brick offset to 0, set city offset to 41
		brick_offset = 0;
		city_offset = FOREGROUND_TILES_SIZE;
		SetTileTable(foreground_tiles);
	}
}

/**
 * \brief Randomly selects which sky should be drawn, dusk or night.
 */
void randomSky(void)
{
	if(prng()&1)
		current_sky = DUSK;
	else
		current_sky = NIGHT;
	setBGTiles(current_sky);
}
