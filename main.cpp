/*
10.27 10��30 ��������
��rush����
��һЩ������У�������Ҫ���䣬��Ҫ���

10.28 10:00
��ֻ��һ��ǽ����������˲���
�������ص����

���䴦����Ҫ���� ���˾������� ���˷���һ��
��������������ʱ��ǰ�������һ����ֱ�ӳ�����ģ�������û���Թ�
*/
#define _BOTZONE_ONLINE
#include <stack>
#include <vector>
#include <set>
#include <string>
#include <iostream>
#include <ctime>
#include <queue>
#include <cstring>
#include <climits>
#include "jsoncpp/json.h"

#define min(a,b) ((a)<(b)?(a):(b))
#define max(a,b) ((a)>(b)?(a):(b))
using std::string;
using std::cin;
using std::cout;
using std::endl;
using std::vector;
using std::flush;
using std::getline;

namespace TankGame
{
	using std::stack;
	using std::set;
	using std::istream;

#ifdef _MSC_VER
#pragma region ���������˵��
#endif

	enum GameResult
	{
		NotFinished = -2,
		Draw = -1,
		Blue = 0,
		Red = 1
	};

	enum FieldItem
	{
		None = 0,
		Brick = 1,
		Steel = 2,
		Base = 4,
		Blue0 = 8,
		Blue1 = 16,
		Red0 = 32,
		Red1 = 64
	};

	template<typename T> inline T operator~ (T a) { return (T)~(int)a; }
	template<typename T> inline T operator| (T a, T b) { return (T)((int)a | (int)b); }
	template<typename T> inline T operator& (T a, T b) { return (T)((int)a & (int)b); }
	template<typename T> inline T operator^ (T a, T b) { return (T)((int)a ^ (int)b); }
	template<typename T> inline T& operator|= (T& a, T b) { return (T&)((int&)a |= (int)b); }
	template<typename T> inline T& operator&= (T& a, T b) { return (T&)((int&)a &= (int)b); }
	template<typename T> inline T& operator^= (T& a, T b) { return (T&)((int&)a ^= (int)b); }

	enum Action
	{
		Invalid = -2,
		Stay = -1,
		Up, Right, Down, Left,
		UpShoot, RightShoot, DownShoot, LeftShoot
	};

	// �������Ͻ�Ϊԭ�㣨0, 0����x ���������죬y ����������
	// Side����ս˫���� - 0 Ϊ����1 Ϊ��
	// Tank��ÿ����̹�ˣ� - 0 Ϊ 0 ��̹�ˣ�1 Ϊ 1 ��̹��
	// Turn���غϱ�ţ� - �� 1 ��ʼ

	const int fieldHeight = 9, fieldWidth = 9, sideCount = 2, tankPerSide = 2;

	// ���صĺ�����
	const int baseX[sideCount] = { fieldWidth / 2, fieldWidth / 2 };

	// ���ص�������
	const int baseY[sideCount] = { 0, fieldHeight - 1 };

	const int dx[4] = { 0, 1, 0, -1 }, dy[4] = { -1, 0, 1, 0 };
	const FieldItem tankItemTypes[sideCount][tankPerSide] = {
		{ Blue0, Blue1 },{ Red0, Red1 }
	};

#ifdef _MSC_VER
#pragma endregion

#pragma region ���ߺ�������
#endif

	inline bool ActionIsMove(Action x)
	{
		return x >= Up && x <= Left;
	}

	inline bool ActionIsShoot(Action x)
	{
		return x >= UpShoot && x <= LeftShoot;
	}

	inline bool ActionDirectionIsOpposite(Action a, Action b)
	{
		return a >= Up && b >= Up && (a + 2) % 4 == b % 4;
	}

	inline bool CoordValid(int x, int y)
	{
		return x >= 0 && x < fieldWidth && y >= 0 && y < fieldHeight;
	}

	// �ж� item �ǲ��ǵ���һ��Ķ��̹��
	inline bool HasMultipleTank(FieldItem item)
	{
		// ���������ֻ��һ���������ô item ��ֵ�� 2 ���ݻ� 0
		// �������� x��x & (x - 1) == 0 ���ҽ��� x �� 2 ���ݻ� 0
		return !!(item & (item - 1));
	}

	inline int GetTankSide(FieldItem item)
	{
		return item == Blue0 || item == Blue1 ? Blue : Red;
	}

	inline int GetTankID(FieldItem item)
	{
		return item == Blue0 || item == Red0 ? 0 : 1;
	}

	// ��ö����ķ���
	inline int ExtractDirectionFromAction(Action x)
	{
		if (x >= Up)
			return x % 4;
		return -1;
	}

	// �����ʧ�ļ�¼�����ڻ���
	struct DisappearLog
	{
		FieldItem item;

		// ��������ʧ�Ļغϵı��
		int turn;

		int x, y;
		bool operator< (const DisappearLog& b) const
		{
			if (x == b.x)
			{
				if (y == b.y)
					return item < b.item;
				return y < b.y;
			}
			return x < b.x;
		}
	};

#ifdef _MSC_VER
#pragma endregion

#pragma region TankField ��Ҫ�߼���
#endif

	class TankField
	{
	public:
		//!//!//!// ���±������Ϊֻ�������Ƽ������޸� //!//!//!//

		// ��Ϸ�����ϵ������һ�������Ͽ����ж��̹�ˣ�
		FieldItem gameField[fieldHeight][fieldWidth] = {};

		// ̹���Ƿ���
		bool tankAlive[sideCount][tankPerSide] = { { true, true },{ true, true } };

		// �����Ƿ���
		bool baseAlive[sideCount] = { true, true };

		// ̹�˺����꣬-1��ʾ̹����ը
		int tankX[sideCount][tankPerSide] = {
			{ fieldWidth / 2 - 2, fieldWidth / 2 + 2 },{ fieldWidth / 2 + 2, fieldWidth / 2 - 2 }
		};

		// ̹�������꣬-1��ʾ̹����ը
		int tankY[sideCount][tankPerSide] = { { 0, 0 },{ fieldHeight - 1, fieldHeight - 1 } };

		// ��ǰ�غϱ��
		int currentTurn = 1;

		// ������һ��
		int mySide;

		// ���ڻ��˵�log
		stack<DisappearLog> logs;

		Action previousActions[101][sideCount][tankPerSide] = { { { Stay, Stay },{ Stay, Stay } } };

		//!//!//!// ���ϱ������Ϊֻ�������Ƽ������޸� //!//!//!//

		// ���غ�˫������ִ�еĶ�������Ҫ�ֶ�����
		Action nextAction[sideCount][tankPerSide] = { { Invalid, Invalid },{ Invalid, Invalid } };

		// �ж���Ϊ�Ƿ�Ϸ���������ƶ����ǿո��������Ƿ���
		// δ����̹���Ƿ���
		bool ActionIsValid(int side, int tank, Action act,int xx=-1,int yy=-1)
		{
		    if (xx==-1 && yy==-1)
            {
                xx = tankX[side][tank];
                yy = tankY[side][tank];
            }
			if (act == Invalid)
				return false;
            //cout<<previousActions[currentTurn - 1][side][tank]<<endl;
			if (act > Left && previousActions[currentTurn - 1][side][tank] > Left) // �������غ����
				return false;

            if (act == Stay || act > Left)
				return true;
            int x,y;
            if(act <= Left)
            {
                x = xx + dx[act];
				y = yy + dy[act];
				return CoordValid(x, y) && gameField[y][x] == None;
            }
            else{
                x = xx + dx[act%4];
				y = yy + dy[act%4];
            }
            if(act > Left && x == baseX[side] && y == baseY[side]) return false;
            return   CoordValid(x,y) && gameField[y][x] != Steel && gameField[y][x] != (Brick<<(3+(!tank) + 2*mySide));
		}

		// �ж� nextAction �е�������Ϊ�Ƿ񶼺Ϸ�
		// ���Ե�δ����̹��
		bool ActionIsValid()
		{
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
					if (tankAlive[side][tank] && !ActionIsValid(side, tank, nextAction[side][tank]))
						return false;
			return true;
		}

	private:
		void _destroyTank(int side, int tank)
		{
			tankAlive[side][tank] = false;
			tankX[side][tank] = tankY[side][tank] = -1;
		}

		void _revertTank(int side, int tank, DisappearLog& log)
		{
			int &currX = tankX[side][tank], &currY = tankY[side][tank];
			if (tankAlive[side][tank])
				gameField[currY][currX] &= ~tankItemTypes[side][tank];
			else
				tankAlive[side][tank] = true;
			currX = log.x;
			currY = log.y;
			gameField[currY][currX] |= tankItemTypes[side][tank];
		}
	public:

		// ִ�� nextAction ��ָ������Ϊ��������һ�غϣ�������Ϊ�Ƿ�Ϸ�
		bool DoAction()
		{
		    //std::cerr<<"DOACTION"<<currentTurn<<endl;
			if (!ActionIsValid())
            {
                DebugPrint();
                std::cerr<<nextAction[!mySide][0]<<" "<<nextAction[!mySide][1]<<endl;
                std::cerr<<"INVALID_ACTION!"<<endl;
				return false;
            }

			// 1 �ƶ�
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					Action act = nextAction[side][tank];

					// ���涯��
					previousActions[currentTurn][side][tank] = act;
					if (tankAlive[side][tank] && ActionIsMove(act))
					{
						int &x = tankX[side][tank], &y = tankY[side][tank];
						FieldItem &items = gameField[y][x];

						// ��¼ Log
						DisappearLog log;
						log.x = x;
						log.y = y;
						log.item = tankItemTypes[side][tank];
						log.turn = currentTurn;
						logs.push(log);

						// �������
						x += dx[act];
						y += dy[act];

						// ������ǣ�ע����ӿ����ж��̹�ˣ�
						gameField[y][x] |= log.item;
						items &= ~log.item;
					}
				}

			// 2 ����
			set<DisappearLog> itemsToBeDestroyed;
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					Action act = nextAction[side][tank];
					if (tankAlive[side][tank] && ActionIsShoot(act))
					{
						int dir = ExtractDirectionFromAction(act);
						int x = tankX[side][tank], y = tankY[side][tank];
						bool hasMultipleTankWithMe = HasMultipleTank(gameField[y][x]);
						while (true)
						{
							x += dx[dir];
							y += dy[dir];
							if (!CoordValid(x, y))
								break;
							FieldItem items = gameField[y][x];
							if (items != None)
							{
								// �����ж�
								if (items >= Blue0 &&
									!hasMultipleTankWithMe && !HasMultipleTank(items))
								{
									// �Լ�������䵽��Ŀ����Ӷ�ֻ��һ��̹��
									Action theirAction = nextAction[GetTankSide(items)][GetTankID(items)];
									if (ActionIsShoot(theirAction) &&
										ActionDirectionIsOpposite(act, theirAction))
									{
										// �����ҷ��ͶԷ�����������Ƿ���
										// ��ô�ͺ���������
										break;
									}
								}

								// �����Щ���Ҫ���ݻ��ˣ���ֹ�ظ��ݻ٣�
								for (int mask = 1; mask <= Red1; mask <<= 1)
									if (items & mask)
									{
										DisappearLog log;
										log.x = x;
										log.y = y;
										log.item = (FieldItem)mask;
										log.turn = currentTurn;
										itemsToBeDestroyed.insert(log);
									}
								break;
							}
						}
					}
				}

			for (auto& log : itemsToBeDestroyed)
			{
				switch (log.item)
				{
				case Base:
				{
					int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
					baseAlive[side] = false;
					break;
				}
				case Blue0:
					_destroyTank(Blue, 0);
					break;
				case Blue1:
					_destroyTank(Blue, 1);
					break;
				case Red0:
					_destroyTank(Red, 0);
					break;
				case Red1:
					_destroyTank(Red, 1);
					break;
				case Steel:
					continue;
				default:
					;
				}
				gameField[log.y][log.x] &= ~log.item;
				logs.push(log);
			}

			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
					nextAction[side][tank] = Invalid;

			currentTurn++;
			return true;
		}

		// �ص���һ�غ�
		bool Revert()
		{
		    //std::cerr<<"REVERT"<<currentTurn<<endl;
			if (currentTurn == 1)
				return false;

			currentTurn--;
			while (!logs.empty())
			{
				DisappearLog& log = logs.top();
				if (log.turn == currentTurn)
				{
					logs.pop();
					switch (log.item)
					{
					case Base:
					{
						int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
						baseAlive[side] = true;
						gameField[log.y][log.x] = Base;
						break;
					}
					case Brick:
						gameField[log.y][log.x] = Brick;
						break;
					case Blue0:
						_revertTank(Blue, 0, log);
						break;
					case Blue1:
						_revertTank(Blue, 1, log);
						break;
					case Red0:
						_revertTank(Red, 0, log);
						break;
					case Red1:
						_revertTank(Red, 1, log);
						break;
					default:
						;
					}
				}
				else
					break;
			}
			return true;
		}

		// ��Ϸ�Ƿ������˭Ӯ�ˣ�
		GameResult GetGameResult()
		{
			bool fail[sideCount] = {};
			for (int side = 0; side < sideCount; side++)
				if ((!tankAlive[side][0] && !tankAlive[side][1]) || !baseAlive[side])
					fail[side] = true;
			if (fail[0] == fail[1])
				return fail[0] || currentTurn > 100 ? Draw : NotFinished;
			if (fail[Blue])
				return Red;
			return Blue;
		}

		// ���� int ��ʾ���� 01 ����ÿ�� int �� 27 λ��ʾ 3 �У�
		TankField(int hasBrick[3], int mySide) : mySide(mySide)
		{
			for (int i = 0; i < 3; i++)
			{
				int mask = 1;
				for (int y = i * 3; y < (i + 1) * 3; y++)
				{
					for (int x = 0; x < fieldWidth; x++)
					{
						if (hasBrick[i] & mask)
							gameField[y][x] = Brick;
						mask <<= 1;
					}
				}
			}
			for (int side = 0; side < sideCount; side++)
			{
				for (int tank = 0; tank < tankPerSide; tank++)
					gameField[tankY[side][tank]][tankX[side][tank]] = tankItemTypes[side][tank];
				gameField[baseY[side]][baseX[side]] = Base;
			}
			gameField[baseY[0] + 1][baseX[0]] = gameField[baseY[1] - 1][baseX[1]] = Steel;
		}

		// ��ӡ����
		void DebugPrint()
		{
#ifdef _BOTZONE_ONLINE
			const string side2String[] = { "Blue", "Red" };
			const string boolean2String[] = { "Dead", "Alived" };
			const char* boldHR = "==============================";
			const char* slimHR = "------------------------------";
			std::cerr << boldHR << endl
				<< "ͼ����" << endl
				<< ". - ��\t# - ש\t% - ��\t* - ����\t@ - ���̹��" << endl
				<< "b - ��0\tB - ��1\tr - ��0\tR - ��1" << endl
				<< slimHR << endl;
			for (int y = 0; y < fieldHeight; y++)
			{
				for (int x = 0; x < fieldWidth; x++)
				{
					switch (gameField[y][x])
					{
					case None:
						std::cerr << '.';
						break;
					case Brick:
						std::cerr << '#';
						break;
					case Steel:
						std::cerr << '%';
						break;
					case Base:
						std::cerr << '*';
						break;
					case Blue0:
						std::cerr << 'b';
						break;
					case Blue1:
						std::cerr << 'B';
						break;
					case Red0:
						std::cerr << 'r';
						break;
					case Red1:
						std::cerr << 'R';
						break;
					default:
						std::cerr << '@';
						break;
					}
				}
				std::cerr << endl;
			}
			std::cerr << slimHR << endl;
			for (int side = 0; side < sideCount; side++)
			{
				std::cerr << side2String[side] << ":Base" << boolean2String[baseAlive[side]];
				for (int tank = 0; tank < tankPerSide; tank++)
					std::cerr << ",tank" << tank << boolean2String[tankAlive[side][tank]];
				std::cerr << endl;
			}
			std::cerr << "currentTurn" << currentTurn << "��";
			GameResult result = GetGameResult();
			if (result == -2)
				std::cerr <<"Going" << endl;
			else if (result == -1)
				std::cerr << "Equal" << endl;
			else
				std::cerr << side2String[result] << "win" << endl;
			std::cerr << boldHR << endl;
#endif
		}

		int dis(int x0,int y0,int x1,int y1)
		{
            if(x0==x1)
            {
                int c = 0;
                for(int i=min(y0,y1) + 1;i<max(y0,y1);i++)
                {
                    if(gameField[i][x0] != None)
                        c++;
                }
                return c;
            }
            else if(y0 == y1)
            {
                int c = 0;
                for(int i=min(x0,x1) + 1;i<max(x0,x1);i++)
                {
                    if(gameField[y0][i] != None)
                        c++;
                }
                return c;
            }
		}

		int rush(int id,int side)
		{
		    int x0=0,y0,best0=INT_MAX;
            y0 = side ? 0 : 8;
            bool flag[2] = {false,false};
            if(tankAlive[side][id] == false)
            {
                return 1000000;
            }
            if(tankAlive[side][id]  && tankY[side][id] == y0){
                nextAction[side][id] = tankX[side][id] < baseX[!side] ? RightShoot : LeftShoot;
                if (nextAction[side][id] > Left && previousActions[currentTurn - 1][side][id] > Left)
                    nextAction[side][id] = Stay;
                int c = dis(tankX[side][id],tankY[side][id],baseX[!side],baseY[!side]);
                if(c==0)return -10000000;
                return c;
			}
			int mp[2][9][9]={0};
			Action from[2][9][9]={};
			std::queue<std::pair<int,int> > q;
            int x,y;
				x = tankX[side][id];
				y = tankY[side][id];
				q.push(std::make_pair(x,y));
				mp[id][x][y] = 1;
				while(!q.empty())
				{
					x = q.front().first; y = q.front().second; q.pop();
					//cout<<x<<"  "<<y<<endl;
                    for(Action act = Up; act <= Left; act=(Action)((int)act+1))
					{
                            int dx,dy;
                            switch(act )
                            {
                            case Up:
                                dx = 0;dy = -1;break;
                            case Right:
                                dx = 1;dy = 0; break;
                            case Down:
                                dx = 0;dy = 1; break;
                            case Left:
                                dx = -1;dy = 0; break;
                            }
                            if(CoordValid(x+dx, y+dy) && (gameField[y+dy][x+dx] == None || gameField[y+dy][x+dx]==Blue0
                                                          ||gameField[y+dy][x+dx]==Blue1||gameField[y+dy][x+dx]==Red0
                                                          ||gameField[y+dy][x+dx]==Red1)){
                                if(mp[id][x+dx][y+dy] == 0 || mp[id][x+dx][y+dy]>mp[id][x][y] + 1)
                                {
                                    mp[id][x+dx][y+dy] = mp[id][x][y] + 1;
                                    from[id][x+dx][y+dy] = act;
                                    q.push(std::make_pair(x+dx,y+dy));
                                }
                            }
                            else if(CoordValid(x+dx, y+dy) && gameField[y+dy][x+dx] != Steel){
                                if(mp[id][x+dx][y+dy] == 0 || mp[id][x+dx][y+dy]>mp[id][x][y] + 2)
                                {
                                    mp[id][x+dx][y+dy] = mp[id][x][y] + 2;
                                    from[id][x+dx][y+dy] = act;
                                    q.push(std::make_pair(x+dx,y+dy));
                                }
                            }
					}
				}
            for(int i = 0; i<9; i++)
            {
                if(mp[id][i][y0] + dis(i,y0,baseX[!side],baseY[!side]) < best0 && mp[id][i][y0]!= 0)
                {
                    best0 = mp[id][i][y0]+ dis(i,y0,baseX[!side],baseY[!side]);
                    x0 = i;
                }
            }
            //cout<<x0<<endl;
            x = x0;
            y = y0;
            Action act;
            while(x != tankX[side][id] || y!=tankY[side][id])
            {
                //cout<<x<<" "<<y<<endl;
                act = from[id][x][y];
                x -= dx[act%4];
                y -= dy[act%4];
            }
            //cout<<3<<endl;
            if(gameField[y+dy[act%4]][x+dx[act%4]] != None)
                nextAction[side][id] = (Action)((int)act + 4);
            else nextAction[side][id] = act;
            if (nextAction[side][id] > Left && previousActions[currentTurn - 1][side][id] > Left)
                nextAction[side][id] = Stay;
            //cout<<nextAction[side][id] <<endl;
            return best0;
		}

		std::pair<int,int> face(int id,int side,int x,int y)
		{
		    int zongflag=0;
			int zongf0 = 0;
		    if(x==tankX[!side][0]){
                int flag=1;
				int f0 = 1;
				int c = 0;
                for(int i=min(y,tankY[!side][0])+1;i<max(y,tankY[!side][0]);i++)
                {
				if(gameField[i][x] == Brick)
					{c++;}
				else if(gameField[i][x] != None)
					{c+=2;}
				}
				if(c >= 1) flag = 0;
				if(c >= 2) f0 = 0;
				if(flag > zongflag) zongflag = flag;
				if(f0 > zongf0) zongf0 = f0;
		    }
		    if(y==tankY[!side][0]){   //ɾ����3��else
		        int flag=2;
				int f0 = 2;
				int c = 0;
                for(int i=min(x,tankX[!side][0])+1;i<max(x,tankX[!side][0]);i++)
                {
				if(gameField[y][i] == Brick)
					{c++;}
				else if(gameField[y][i] != None)
					{c+=2;}
				}
				if(c >= 1) flag = 0;
				if(c >= 2) f0 = 0;
				if(flag > zongflag) zongflag = flag;
				if(f0 > zongf0) zongf0 = f0;
		    }
		    if(x==tankX[!side][1]){
		        int flag=3;
				int f0 = 3;
				int c = 0;
                for(int i=min(y,tankY[!side][1])+1;i<max(y,tankY[!side][1]);i++)
                {
				if(gameField[i][x] == Brick)
					{c++;}
				else if(gameField[i][x] != None)
					{c+=2;}
				}
				if(c >= 1) flag = 0;
				if(c >= 2) f0 = 0;
				if(flag > zongflag) zongflag = flag;
				if(f0 > zongf0) zongf0 = f0;
		    }
		    if(y==tankY[!side][1]){
		        int flag=4;
				int f0 = 4;
				int c = 0;
                for(int i=min(x,tankX[!side][1])+1;i<max(x,tankX[!side][1]);i++)
                {
				if(gameField[y][i] == Brick)
					{c++;}
				else if(gameField[y][i] != None)
					{c+=2;}
				}
				if(c >= 1) flag = 0;
				if(c >= 2) f0 = 0;
				if(flag > zongflag) zongflag = flag;
				if(f0 > zongf0) zongf0 = f0;
		    }
		    return std::make_pair(zongflag,zongf0);
		}

		void spe_judge(int id,int side){
                int flag,f0;
                int x=tankX[side][id],y=tankY[side][id];
                //�ж��Ƿ��ֱ�������������,labelΪfalse��ʾ����
                bool label = true;
                flag = face(id,side,x,y).first;
                if( x == baseX[!side])
                {
                    int c = 0;
                    for(int i=min(y,baseY[!side]) + 1;i<max(y,baseY[!side]);i++)
                    {
                        if(gameField[i][x] != None)
                            c++;
                    }
                    if(c == 0) {
                        if(previousActions[currentTurn - 1][side][id] <= Left)
                        {
                            nextAction[side][id] = y < baseY[!side] ? DownShoot : UpShoot;
                            label = false;
                        }
                        else nextAction[side][id] = Stay;
                    }
                }
                else if(y == baseY[!side])
                {
                    int c = 0;
                    for(int i=min(x,baseX[!side]) + 1;i<max(x,baseX[!side]);i++)
                    {
                        if(gameField[y][i] != None)
                            c++;
                    }
                    if(c == 0)  {
                        if(previousActions[currentTurn - 1][side][id] <= Left)
                        {
                            nextAction[side][id] = x > baseX[!side] ? LeftShoot : RightShoot;
                            label = false;
                        }
                        else nextAction[side][id] = Stay;
                    }
                }
                if(label ==false) {}
                else if(flag){                   //���ԺͶ��ֶ��� ����û��Ҫ����rush
                    if(previousActions[currentTurn - 1][side][id] <= Left){
                         if(flag == 1){
                            if(nextAction[side][id] !=Left && nextAction[side][id] != Right)
                                nextAction[side][id] = y<tankY[!side][0] ? DownShoot : UpShoot;
                        }
                        else if(flag == 3){
                            if(nextAction[side][id] !=Left && nextAction[side][id] != Right)
                                nextAction[side][id] =y<tankY[!side][1] ? DownShoot : UpShoot;
                        }
                       else if(flag == 2){
                            if(nextAction[side][id] !=Up && nextAction[side][id] != Down)
                                nextAction[side][id] = x>tankX[!side][0] ? LeftShoot : RightShoot;
                            if(x == tankX[!side][0])                          //�ص�ʱԤ�г�����rush�ķ������
                                nextAction[side][id] = side ?  DownShoot : UpShoot;
                        }
                        else if(flag == 4){
                            if(nextAction[side][id] !=Up && nextAction[side][id] != Down)
                                nextAction[side][id] = x>tankX[!side][1] ? LeftShoot : RightShoot;
                            if(x == tankX[!side][1])
                                nextAction[side][id] = side ?  DownShoot : UpShoot;
                        }
                    }
                    else{               //�Ҳ��� �Է����� �;������
                        if(previousActions[currentTurn - 1][!side][0] <= Left){
                            if(flag == 1){
                                int tmp= x>baseX[side]? -1 : 1;
                                if(CoordValid(x+tmp, y) && gameField[y][x+tmp] == None)
                                    nextAction[side][id] = tmp==1? Right : Left;
                                else if(CoordValid(x-tmp, y) && gameField[y][x-tmp] == None)
                                    nextAction[side][id] = tmp==1? Left : Right;
                            }
                            else if(flag == 2){
                                int tmp= side? -1 :1;
                                if(CoordValid(x, y+tmp) && gameField[y+tmp][x] == None)
                                    nextAction[side][id] = tmp==1?Down : Up;
                                else if(CoordValid(x, y-tmp) && gameField[y-tmp][x] == None)
                                    nextAction[side][id] = tmp==1?Up :Down;
                            }
                        }
                        if(previousActions[currentTurn - 1][!side][1] <= Left){
                            if(flag == 3){
                                if(CoordValid(x+1, y) && gameField[y][x+1] == None)
                                    nextAction[side][id] = Right;
                                else if(CoordValid(x-1, y) && gameField[y][x-1] == None)
                                    nextAction[side][id] = Left;
                            }
                            else if(flag == 4){
                                if(CoordValid(x, y+1) && gameField[y+1][x] == None)
                                    nextAction[side][id] = Down;
                                else if(CoordValid(x, y-1) && gameField[y-1][x] == None)
                                    nextAction[side][id] = Up;
                            }
                        }
                    }
                }
                else if( nextAction[side][id] <=Left &&nextAction[side][id] >=Up){                //��һ������������
                    x=tankX[side][id] + dx[nextAction[side][id]];
                    y=tankY[side][id] + dy[nextAction[side][id]];
                    if(flag = face(id,side,x,y).first){
                        if(flag == 1 || flag == 2){
                            if(previousActions[currentTurn - 1][!side][0] <= Left){
                                if((rand()%100) >50)
                                    nextAction[side][id] = Stay;
                            }
                        }
                        else{
                             if(previousActions[currentTurn - 1][!side][1] <= Left){
                                if((rand()%100) >50)
                                    nextAction[side][id] = Stay;
                            }
                        }
                    }
                }

				 //�Ͷ��������ֻ����һ��ǽ
				else if(f0 = face(id,side,x,y).second)
				{
				    //cout<<nextAction[side][id]<<endl;
					if(nextAction[side][id] > Left)
					{                                   //����Χ��ǽ�ȿ��� ����Χ�Ļ�����ֱ���
					    if(f0 == 1 || f0 ==3){
                            if(CoordValid(x+1, y) && gameField[y][x+1] == Brick && x > baseX[side]+1)
                                nextAction[side][id] = RightShoot;
                            else if(CoordValid(x-1, y) && gameField[y][x-1] == Brick && x < baseX[side]-1)
                                nextAction[side][id] = LeftShoot;
                            else nextAction[side][id] = Stay;
					    }
					    else if(f0 == 2 || f0 == 4){
                            if(CoordValid(x, y+1) && gameField[y+1][x] == Brick && !side)
                                nextAction[side][id] = DownShoot;
                            else if(CoordValid(x, y-1) && gameField[y-1][x] == Brick && side)
                                nextAction[side][id] = UpShoot;
                            else nextAction[side][id] = Stay;
					    }
					}
				}
		}
		vector<int> dfs(int side,int depth)
        {

            if(depth == 2)
            {
                //cout<<rush(0,side)<<" "<<rush(1,side)<<"_____"<<endl;
                return {rush(0,side),rush(1,side)};
            }
            int best0  = 1000000,best1 = 1000000,best2 = 1000000,best3 = 1000000;
            const Action actcons[9] = {UpShoot,RightShoot,DownShoot,LeftShoot,Up,Right,Down,Left,Stay};
            Action bestact0=Stay,bestact1=Stay,bestact2=Stay,bestact3=Stay;
            Action act0,act1,act2,act3;
            for(int i = 0;i<9;i++)
            if(ActionIsValid(side,0,act0 = actcons[i])){
                for(int j = 0;j<9;j++)
                if(ActionIsValid(side,1,act1 = actcons[j]) )
                {
                    /*if(currentTurn < 5)
                    {
                        std::cerr<<"!!"<<endl;
                    }*/
                    //if(depth==0)
                    //std::cerr<<currentTurn<<" "<<act1<<" "<<previousActions[currentTurn - 1][side][1]<<endl;
                    {//cout<<side<<" "<<depth<<" "<<act0<<" "<<act1<<endl;
                        nextAction[side][0] = act0;
                        nextAction[side][1] = act1;
                        int tmp2= rush(0,!side);
                        spe_judge(0,!side);
                        int tmp3 = rush(1,!side);
                        spe_judge(1,!side);
                        act2 = nextAction[!side][0];
                        act3 = nextAction[!side][1];
                        DoAction();
                        auto tmp = dfs(side, depth+1);
                        if( tmp[0] + tmp[1]< best0+best1 || (tmp[0] + tmp[1] == best0 +best1 &&tmp2+tmp3>(best2+best3)))  //�����õ��ж�0��1Ӧ������ϵ,��Ҫ��
                        {
                            //std::cerr<<depth<<" "<<tmp[0]<<" "<<tmp[1]<<" "<<act0<<" "<<act1<<endl;

                            best0 = tmp[0];
                            bestact0 = act0;
                            best1 = tmp[1];
                            bestact1 = act1;
                            best2 = tmp2;
                            bestact2 = act2;
                            best3 = tmp3;
                            bestact3 = act3;
                            //std::cerr<<"bestact0 "<<bestact0<<" bestact1 "<<bestact1<<" bestact2 "<<bestact2<<" bestact3 "<<bestact3<<endl;
                            //cout<<0<<" "<<best0<<" "<<bestact0<<endl;
                        }/*
                        if( tmp[1] < best1)
                        {
                            cout<<1<<" "<<best1<<" "<<bestact1<<endl;
                        }
                        if( tmp[2] < best2)  //�����õ��ж�0��1Ӧ������ϵ,��Ҫ��
                        {
                            cout<<2<<" "<<best2<<" "<<bestact2<<endl;
                        }
                        if( tmp[3] < best3)
                        {
                            cout<<3<<" "<<best3<<" "<<bestact3<<endl;
                        }*/
                        Revert();
                    }
                }
            }
            if(depth == 0)
            {
                nextAction[side][0] = bestact0;
                nextAction[side][1] = bestact1;
            }
            return {best0,best1};
        }
        int flyto(int id,int side,int posx,int posy)
        {
            int mp[3][10][10]={};
            Action from[2][9][9]={};
			std::queue<std::pair<int,int> > q;
            int x,y;
				x = tankX[side][id];
				y = tankY[side][id];
				q.push(std::make_pair(x,y));
				mp[id][x][y] = 1;
				while(!q.empty())
				{
					x = q.front().first; y = q.front().second; q.pop();
					//cout<<x<<"  "<<y<<endl;
                    for(Action act = Up; act <= Left; act=(Action)((int)act+1))
					{
                            int dx,dy;
                            switch(act )
                            {
                            case Up:
                                dx = 0;dy = -1;break;
                            case Right:
                                dx = 1;dy = 0; break;
                            case Down:
                                dx = 0;dy = 1; break;
                            case Left:
                                dx = -1;dy = 0; break;
                            }
                            if(CoordValid(x+dx, y+dy) && (gameField[y+dy][x+dx] == None || gameField[y+dy][x+dx]==Blue0
                                                          ||gameField[y+dy][x+dx]==Blue1||gameField[y+dy][x+dx]==Red0
                                                          ||gameField[y+dy][x+dx]==Red1)){
                                if(mp[id][x+dx][y+dy] == 0 || mp[id][x+dx][y+dy]>mp[id][x][y] + 1)
                                {
                                    mp[id][x+dx][y+dy] = mp[id][x][y] + 1;
                                    from[id][x+dx][y+dy] = act;
                                    q.push(std::make_pair(x+dx,y+dy));
                                }
                            }
                            else if(CoordValid(x+dx, y+dy) && gameField[y+dy][x+dx] != Steel){
                                if(mp[id][x+dx][y+dy] == 0 || mp[id][x+dx][y+dy]>mp[id][x][y] + 2)
                                {
                                    mp[id][x+dx][y+dy] = mp[id][x][y] + 2;
                                    from[id][x+dx][y+dy] = act;
                                    q.push(std::make_pair(x+dx,y+dy));
                                }
                            }
					}
				}
            x = posx;
            y = posy;
            Action act;
            while(x != tankX[side][id] || y!=tankY[side][id])
            {
                //cout<<x<<" "<<y<<endl;
                act = from[id][x][y];
                x -= dx[act%4];
                y -= dy[act%4];
            }
            //cout<<3<<endl;
            if(gameField[y+dy[act%4]][x+dx[act%4]] != None)
                nextAction[side][id] = (Action)((int)act + 4);
            else nextAction[side][id] = act;
            if (nextAction[side][id] > Left && previousActions[currentTurn - 1][side][id] > Left)
                nextAction[side][id] = Stay;
            return mp[id][posx][posy];
        }
        void defend(int id,int side)
        {
            int posx = baseX[side] + ((side ^ id) ? 1 : -1);
            int posy = baseY[side];
            if( posx != tankX[side][id] || posy!=tankY[side][id])
            {
                flyto(id,side,posx,posy);
                spe_judge(id,side);
            }
            else
            {
                int flag;
                if(flag = face(id,side,posx,posy).first)
                {
                    if(previousActions[currentTurn - 1][side][id] <= Left){
                         if(flag == 1){
                            if(nextAction[side][id] !=Left && nextAction[side][id] != Right)
                                nextAction[side][id] = posy<tankY[!side][0] ? DownShoot : UpShoot;
                        }
                        else if(flag == 3){
                            if(nextAction[side][id] !=Left && nextAction[side][id] != Right)
                                nextAction[side][id] =posy<tankY[!side][1] ? DownShoot : UpShoot;
                        }
                       else if(flag == 2){
                            if(nextAction[side][id] !=Up && nextAction[side][id] != Down)
                                nextAction[side][id] = posx>tankX[!side][0] ? LeftShoot : RightShoot;
                        }
                        else if(flag == 4){
                            if(nextAction[side][id] !=Up && nextAction[side][id] != Down)
                                nextAction[side][id] = posx>tankX[!side][1] ? LeftShoot : RightShoot;
                        }
                    }
                }
                else
                {
                    nextAction[side][id] = Stay;
                }
            }
        }
        int burst(int id,int side)
        {
            if(side==0) return tankY[side][id] - 4;
            else return 4 - tankY[side][id];
        }
        void processor()
        {
            /*
            if(tankAlive[mySide][0]){
                rush(0,mySide);
                spe_judge(0);
            }

            if(tankAlive[mySide][1]){
                rush(1,mySide);
                spe_judge(1);
            }*/
            int guard = 2;
            if(rush(0,mySide) < rush(1,mySide)) guard = 1;
            else if(rush(0,mySide) > rush(1,mySide)) guard = 0;
            if(guard < 2 && rush(guard,mySide) <= rush(!guard,!mySide)) guard = 2;
            if(guard < 2 && !(burst(!guard,!mySide) >=-1 && burst(guard,mySide) <= -1) ) guard = 2;
            if(guard == 2 || !(tankAlive[mySide][0] && tankAlive[mySide][1]))//�����к�Ӧ�÷��ػ��ǽ���?
            {
                dfs(mySide,0);
                std::cerr<<nextAction[mySide][0]<<" "<<nextAction[mySide][1]<<endl;
                if(tankAlive[mySide][0]) spe_judge(0,mySide);
                if(tankAlive[mySide][1]) spe_judge(1,mySide);
            }
            else
            {
                dfs(mySide,0);
                defend(guard,mySide);
                if(tankAlive[mySide][!guard]) spe_judge(!guard,mySide);
            }
        }           //end of processor

        // end of Tank
	};

#ifdef _MSC_VER
#pragma endregion
#endif

	TankField *field;

#ifdef _MSC_VER
#pragma region ��ƽ̨��������
#endif

	// �ڲ�����
	namespace Internals
	{
		Json::Reader reader;
#ifdef _BOTZONE_ONLINE
		Json::FastWriter writer;
#else
		Json::StyledWriter writer;
#endif

		void _processRequestOrResponse(Json::Value& value, bool isOpponent)
		{
			if (value.isArray())
			{
				if (!isOpponent)
				{
					for (int tank = 0; tank < tankPerSide; tank++)
						field->nextAction[field->mySide][tank] = (Action)value[tank].asInt();
				}
				else
				{
					for (int tank = 0; tank < tankPerSide; tank++)
						field->nextAction[1 - field->mySide][tank] = (Action)value[tank].asInt();
					field->DoAction();
				}
			}
			else
			{
				// �ǵ�һ�غϣ������ڽ��ܳ���
				int hasBrick[3];
				for (int i = 0; i < 3; i++)
					hasBrick[i] = value["field"][i].asInt();
				field = new TankField(hasBrick, value["mySide"].asInt());
			}
		}

		// ��ʹ�� SubmitAndExit ���� SubmitAndDontExit
		void _submitAction(Action tank0, Action tank1, string debug = "", string data = "", string globalData = "")
		{
			Json::Value output(Json::objectValue), response(Json::arrayValue);
			response[0U] = tank0;
			response[1U] = tank1;
			output["response"] = response;
			if (!debug.empty())
				output["debug"] = debug;
			if (!data.empty())
				output["data"] = data;
			if (!globalData.empty())
				output["globalData"] = globalData;
			cout << writer.write(output) << endl;
		}
	}

	// �������������� cin ���� fstream����ȡ�غ���Ϣ������ TankField������ȡ�ϻغϴ洢�� data �� globaldata
	// ���ص��Ե�ʱ��֧�ֶ��У��������һ����Ҫ��û��������һ��"}"��"]"��β
	void ReadInput(istream& in, string& outData, string& outGlobalData)
	{
		Json::Value input;
		string inputString;
		do
		{
			getline(in, inputString);
		} while (inputString.empty());
#ifndef _BOTZONE_ONLINE
		// �²��ǵ��л��Ƕ���
		char lastChar = inputString[inputString.size() - 1];
		if (lastChar != '}' && lastChar != ']')
		{
			// ��һ�в���}��]��β���²��Ƕ���
			string newString;
			do
			{
				getline(in, newString);
				inputString += newString;
			} while (newString != "}" && newString != "]");
		}
#endif
		Internals::reader.parse(inputString, input);

		if (input.isObject())
		{
			Json::Value requests = input["requests"], responses = input["responses"];
			if (!requests.isNull() && requests.isArray())
			{
				size_t i, n = requests.size();
				for (i = 0; i < n; i++)
				{
					Internals::_processRequestOrResponse(requests[i], true);
					if (i < n - 1)
						Internals::_processRequestOrResponse(responses[i], false);
				}
				outData = input["data"].asString();
				outGlobalData = input["globaldata"].asString();
				return;
			}
		}
		Internals::_processRequestOrResponse(input, true);
	}

	// �ύ���߲��˳����»غ�ʱ���������г���
	void SubmitAndExit(Action tank0, Action tank1, string debug = "", string data = "", string globalData = "")
	{
		Internals::_submitAction(tank0, tank1, debug, data, globalData);
		exit(0);
	}

	// �ύ���ߣ��»غ�ʱ����������У���Ҫ�� Botzone ���ύ Bot ʱѡ������ʱ���С���
	// �����Ϸ����������ᱻϵͳɱ��
	void SubmitAndDontExit(Action tank0, Action tank1)
	{
		Internals::_submitAction(tank0, tank1);
		field->nextAction[field->mySide][0] = tank0;
		field->nextAction[field->mySide][1] = tank1;
		cout << ">>>BOTZONE_REQUEST_KEEP_RUNNING<<<" << endl;
	}
#ifdef _MSC_VER
#pragma endregion
#endif
	}

int RandBetween(int from, int to)
{
	return rand() % (to - from) + from;
}

TankGame::Action RandAction(int tank)
{
	while (true)
	{
		auto act = (TankGame::Action)RandBetween(TankGame::Stay, TankGame::LeftShoot + 1);
		if (TankGame::field->ActionIsValid(TankGame::field->mySide, tank, act))
			return act;
	}
}



int main()
{
	srand((unsigned)time(nullptr));
	while (true)
	{
		string data, globaldata;
		TankGame::ReadInput(cin, data, globaldata);
		TankGame::field->processor();
		TankGame::SubmitAndExit(TankGame::field->nextAction[TankGame::field->mySide][0], TankGame::field->nextAction[TankGame::field->mySide][1]);
	}
}
