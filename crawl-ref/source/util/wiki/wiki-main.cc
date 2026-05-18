/**
 * @file
 * @brief Contains code for the `wiki` utility.
**/

#include "AppHdr.h"

#include "branch.h"
#include "fake-main.hpp"

#include "coordit.h"
#include "database.h"
#include "describe.h" // get_item_description
#include "fight.h" // spines_damage
#include "files.h"
#include "initfile.h"
#include "item-name.h"
#include "item-prop.h"
#include "items.h"
#include "los.h"
#include "mapdef.h" // item_list
#include "message.h"
#include "mon-death.h"
#include "mon-explode.h" // ball_lightning_damage
#include "mon-project.h"
#include "spl-book.h"
#include "spl-damage.h"
#include "spl-summoning.h" // mons_ball_lighting_hd
#include "spl-util.h"
#include "spl-zap.h"
#include "syscalls.h"
#include "tag-version.h"
#include "version.h"

#ifdef _MSC_VER
extern "C" unsigned long long _dtoul3_legacy(double v) { return (unsigned long long)llround(v); }
#endif

const coord_def MONSTER_PLACE(20, 20);
const coord_def WALL_PLACE(30, 30);

const int PLAYER_MAXHP = 500;
const int PLAYER_MAXMP = 50;

static void record_resvul(int color, const char* name, const char* caption,
                          string& str, int rval)
{
    if (str.empty())
        str = " | " + string(caption) + ": ";
    else
        str += ", ";

    if (color && (rval == 3 || rval == 1 && color == BROWN
                  || string(caption) == "Vul")
        && (int)color <= 7)
    {
        color += 8;
    }

    string token(name);
    if (rval > 1 && rval <= 3)
    {
        while (rval-- > 0)
            token += "+";
    }

    str += token;
}

static void monster_action_cost(string& qual, int cost, const char* desc)
{
    if (cost != 10)
    {
        if (!qual.empty())
            qual += "; ";
        qual += desc;
        qual += ": " + to_string(cost * 10) + "%";
    }
}

static string monster_int(const monster& mon)
{
    string intel = "???";
    switch (mons_intel(mon))
    {
    case I_BRAINLESS:
        intel = "brainless";
        break;
    case I_ANIMAL:
        intel = "animal";
        break;
    case I_HUMAN:
        intel = "human";
        break;
        // Let the compiler issue warnings for missing entries.
    }

    return intel;
}

static string monster_size(const monster& mon)
{
    switch (mon.body_size())
    {
    case SIZE_TINY:
        return "tiny";
    case SIZE_LITTLE:
        return "little";
    case SIZE_SMALL:
        return "small";
    case SIZE_MEDIUM:
        return "Medium";
    case SIZE_LARGE:
        return "Large";
    case SIZE_GIANT:
        return "Giant";
    default:
        return "???";
    }
}

static string monster_speed(const monster& mon, int speed_min, int speed_max)
{
    string speed;

    if (speed_max != speed_min)
        speed += to_string(speed_min) + " - " + to_string(speed_max);
    else if (speed_max == 0)
        speed += "0";
    else
        speed += to_string(speed_max);

    const mon_energy_usage& cost = mons_energy(mon);
    string qualifiers;

    bool skip_action = false;
    if (cost.attack != 10 && cost.attack == cost.missile
        && cost.attack == cost.spell)
    {
        monster_action_cost(qualifiers, cost.attack, "act");
        skip_action = true;
    }

    monster_action_cost(qualifiers, cost.move, "move");
    if (cost.swim != cost.move)
        monster_action_cost(qualifiers, cost.swim, "swim");
    if (!skip_action)
    {
        monster_action_cost(qualifiers, cost.attack, "atk");
        monster_action_cost(qualifiers, cost.missile, "msl");
        monster_action_cost(qualifiers, cost.spell, "spell");
    }
    if (speed_max > 0 && mons_class_flag(mon.type, M_STATIONARY))
    {
        if (!qualifiers.empty())
            qualifiers += "; ";
        qualifiers += "stationary";
    }

    if (!qualifiers.empty())
        speed += " (" + qualifiers + ")";

    return speed;
}

static void initialize_crawl()
{
    init_monsters();
    init_properties();
    init_item_name_cache();

    init_zap_index();
    init_spell_descs();
    init_monster_symbols();
    init_mon_name_cache();
    init_spell_name_cache();
    init_mons_spells();
    init_element_colours();
    init_show_table(); // Initializes indices for get_feature_def.
    clua.init_libraries();
    init_dungeon_lua();
    databaseSystemInit();

    dgn_reset_level();
    for (rectangle_iterator ri(0); ri; ++ri)
        env.grid(*ri) = DNGN_FLOOR;
    env.grid(WALL_PLACE) = DNGN_ROCK_WALL;

    los_changed();
    you.hp = you.hp_max = PLAYER_MAXHP;
    you.magic_points = you.max_magic_points = PLAYER_MAXMP;
    you.species = SP_HUMAN;
    you.current_vision = you.normal_vision = LOS_RADIUS; // Workaround for spells to give 8 as range
}

static string dice_def_string(dice_def dice)
{
    return dice.num == 1 ? make_stringf("d%d", dice.size) :
                           make_stringf("%dd%d", dice.num, dice.size);
}

static dice_def mi_calc_iood_damage(monster* mons)
{
    const int pow = mons_power_for_hd(SPELL_IOOD, mons->get_hit_dice());
    return iood_damage(pow, INFINITE_DISTANCE);
}

static string mi_calc_smiting_damage(monster* /*mons*/) { return "7-17"; }

static string mi_calc_brain_bite_damage(monster* /*mons*/) { return "4-8*"; }

static string mi_calc_pyre_arrow_damage(monster* mons)
{
    return make_stringf("2d%d*", 2 + mons->get_hit_dice() * 12 / 14);
}

static string mi_calc_antimagic_gaze_drain(monster* mons)
{
    const int pow = mons_power_for_hd(SPELL_ANTIMAGIC_GAZE, mons->get_hit_dice());
    return make_stringf("0-%d MP", pow / 8);
}

static string mi_calc_airstrike_damage(monster* mons, spell_type spell_cast)
{
    const int pow = mons_power_for_hd(spell_cast, mons->get_hit_dice());
    dice_def dice = base_airstrike_damage(pow);
    return make_stringf("%dd%d+(%d/space)", dice.num, dice.size,
                        spell_cast == SPELL_SLEETSTRIKE ? 3 : 2);
}

static string mi_calc_glaciate_damage(monster* mons)
{
    int pow = 12 * mons->get_experience_level();
    // Minimum of the number of dice, or the max damage at max range
    int minimum = min(10, (54 + 3 * pow / 2) / 6);
    // Maximum damage at minimum range.
    int max = (54 + 3 * pow / 2) / 3;

    return make_stringf("%d-%d", minimum, max);
}

static string mi_calc_chain_lightning_damage(monster* mons)
{
    const spell_type spell = SPELL_CHAIN_LIGHTNING;
    const zap_type zap = spell_to_zap(spell);
    const int pow = mons_power_for_hd(spell, mons->spell_hd(spell));
    const dice_def dice = zap_damage(zap, pow, true, false);
    return dice_def_string(dice);
}

static string mi_calc_vampiric_drain_damage(monster* mons)
{
    int pow = 12 * mons->get_experience_level();

    // The current formula is 3 + random2avg(9, 2) + 1 + random2(pow) / 7.
    // Min is 3 + 0 + 1 + (0 / 7) = 4.
    // Max is 3 + 8 + 1 + (pow - 1) / 7 = 12 + (pow - 1) / 7.
    int min = 4;
    int max = 12 + (pow - 1) / 7;
    return make_stringf("%d-%d", min, max);
}

static string mi_calc_major_healing(monster* mons)
{
    const int min = 50;
    const int max = min + mons->spell_hd(SPELL_MAJOR_HEALING) * 10;
    return make_stringf("%d-%d", min, max);
}

static string mi_calc_scorch_damage(monster* mons)
{
    const int pow = mons_power_for_hd(SPELL_SCORCH, mons->get_hit_dice());
    return dice_def_string(scorch_damage(pow, false));
}

static string mi_calc_irradiate_damage(const monster &mon)
{
    const int pow = mons_power_for_hd(SPELL_IRRADIATE, mon.get_hit_dice());
    return dice_def_string(irradiate_damage(pow));
}

static string mi_calc_resonance_strike_damage(monster* mons)
{
    const int pow = mons->spell_hd(SPELL_RESONANCE_STRIKE);
    dice_def dice = resonance_strike_base_damage(pow);
    return describe_resonance_strike_dam(dice);
}

/**
 * @return e.g.: "2d6", "5-12".
 */
static string mons_human_readable_spell_damage_string(monster* monster,
  spell_type sp)
{
  const int pow = mons_power_for_hd(sp, monster->spell_hd(sp));
  bolt spell_beam = mons_spell_beam(monster, sp, pow, true);
  switch (sp)
  {
  case SPELL_PORTAL_PROJECTILE:
  case SPELL_LRD:
    return ""; // Fake damage beam
  case SPELL_SCORCH:
    return mi_calc_scorch_damage(monster);
  case SPELL_SMITING:
    return mi_calc_smiting_damage(monster);
  case SPELL_BRAIN_BITE:
    return mi_calc_brain_bite_damage(monster);
  case SPELL_PYRE_ARROW:
    return mi_calc_pyre_arrow_damage(monster);
  case SPELL_ANTIMAGIC_GAZE:
    return mi_calc_antimagic_gaze_drain(monster);
  case SPELL_AIRSTRIKE:
  case SPELL_SLEETSTRIKE:
    return mi_calc_airstrike_damage(monster, sp);
  case SPELL_GLACIATE:
    return mi_calc_glaciate_damage(monster);
  case SPELL_CHAIN_LIGHTNING:
    return mi_calc_chain_lightning_damage(monster);
  case SPELL_CONJURE_BALL_LIGHTNING:
    return "3x" + dice_def_string(ball_lightning_damage(mons_ball_lightning_hd(pow, false)));
  case SPELL_MARSHLIGHT:
    return "2x" + dice_def_string(zap_damage(ZAP_FOXFIRE, pow, true));
  case SPELL_PLASMA_BEAM:
    return "2x" + dice_def_string(zap_damage(ZAP_PLASMA, pow, true));
  case SPELL_PERMAFROST_ERUPTION:
    return "2x" + dice_def_string(zap_damage(ZAP_PERMAFROST_ERUPTION_COLD, pow, true));
  case SPELL_WATERSTRIKE:
    spell_beam.damage = waterstrike_damage(monster->spell_hd(sp));
    break;
  case SPELL_RESONANCE_STRIKE:
    return mi_calc_resonance_strike_damage(monster);
  case SPELL_IOOD:
    spell_beam.damage = mi_calc_iood_damage(monster);
    break;
  case SPELL_POLAR_VORTEX:
    return dice_def_string(polar_vortex_dice(pow, true)) + "*";
  case SPELL_IRRADIATE:
    return mi_calc_irradiate_damage(*monster);
  case SPELL_VAMPIRIC_DRAINING:
    return mi_calc_vampiric_drain_damage(monster);
  case SPELL_MAJOR_HEALING:
    return mi_calc_major_healing(monster);
  case SPELL_MINOR_HEALING:
  case SPELL_HEAL_OTHER:
    return dice_def_string(spell_beam.damage) + "+3";

  default:
    break;
  }

  if (spell_beam.damage.size && spell_beam.damage.num)
    return dice_def_string(spell_beam.damage);
  return "";
}

static string _get_monster_spell_flags_description(mon_spell_slot_flags flags)
{
    vector<string> str_flags;

    if (flags & MON_SPELL_EMERGENCY) {
      str_flags.push_back("Emergency");
    }
    if (flags & MON_SPELL_NATURAL) {
      str_flags.push_back("Natural");
    }
    if (flags & MON_SPELL_MAGICAL) {
      str_flags.push_back("Magical");
    }
    if (flags & MON_SPELL_VOCAL) {
      str_flags.push_back("Vocal");
    }
    if (flags & MON_SPELL_WIZARD) {
      str_flags.push_back("Wizard");
    }
    if (flags & MON_SPELL_PRIEST) {
      str_flags.push_back("Priest");
    }
    if (flags & MON_SPELL_BREATH) {
      str_flags.push_back("Breath");
    }
#if TAG_MAJOR_VERSION == 34
    if (flags & MON_SPELL_NO_SILENT) {
      str_flags.push_back("No silent");
    }
#endif
    if (flags & MON_SPELL_INSTANT) {
      str_flags.push_back("Instant");
    }
    if (flags & MON_SPELL_NOISY) {
      str_flags.push_back("Noisy");
    }
    if (flags & MON_SPELL_SHORT_RANGE) {
      str_flags.push_back("Short range");
    }
    if (flags & MON_SPELL_LONG_RANGE) {
      str_flags.push_back("Long range");
    }
    if (flags & MON_SPELL_EVOKE) {
      str_flags.push_back("Evoke");
    }
    if (str_flags.empty()) {
      return "";
    }
    std::string result_string = "[";
    bool first = true;
    for (const auto & flag : str_flags) {
      if (!first) {
        result_string += ", ";
      }
      result_string += make_stringf(R"("%s")", flag.c_str());
      first = false;
    }
    result_string += "]";
    return result_string;
}

static inline void set_min_max(int num, int& min, int& max)
{
    if (!min || num < min)
        min = num;
    if (!max || num > max)
        max = num;
}

static int _mi_create_monster(mons_spec spec)
{
    const auto me = get_monster_data(spec.type);
    auto place = MONSTER_PLACE;
    if (me->habitat == HT_WALLS_ONLY)
    {
      place = WALL_PLACE;
    }
    monster* monster =
        dgn_place_monster(spec, place, true, false, false);
    if (monster)
    {
        monster->behaviour = BEH_SEEK;
        monster->foe = MHITYOU;
        msg::suppress mx;
        return monster->mindex();
    }
    return NON_MONSTER;
}

static string damage_flavour(const string& name,
                                  const string& damage)
{
    return "(" + name + ":" + damage + ")";
}

static string damage_flavour(const string& name, int low, int high)
{
    return make_stringf("(%s:%d-%d)", name.c_str(), low, high);
}

static void _add_quoted_item(std::string& target, std::string new_item)
{
  if (!target.empty())
  {
    target += ", ";
  }
  target += '"' + new_item + '"';
}

// similar to mon_attack_name_short
static const char* _get_mon_attack_type_description(attack_type type)
{
  switch (type)
  {
  case AT_NONE:
    return "None";
  case AT_HIT:
    return "Hit";
  case AT_BITE:
    return "Bite";
  case AT_STING:
    return "Sting";
  case AT_SPORE:
    return "Spore";
  case AT_TOUCH:
    return "Touch";
  case AT_ENGULF:
    return "Engulf";
  case AT_CLAW:
    return "Claw";
  case AT_PECK:
    return "Peck";
  case AT_HEADBUTT:
    return "Headbutt";
  case AT_PUNCH:
    return "Punch";
  case AT_KICK:
    return "Kick";
  case AT_TENTACLE_SLAP:
    return "Tentacle slap";
  case AT_TAIL_SLAP:
    return "Tail slap";
  case AT_GORE:
    return "Gore";
  case AT_CONSTRICT:
    return "Constrict";
  case AT_TRAMPLE:
    return "Trample";
  case AT_TRUNK_SLAP:
    return "Trunk slap";
  case AT_SNAP:
    return "Snap";
  case AT_SPLASH:
    return "Splash";
  case AT_POUNCE:
    return "Pounce";
  case AT_REACH_STING:
    return "Reach sting";
  case AT_CHERUB:
    return "Cherub";
  case AT_SHOOT:
    return "Shoot";
  case AT_WEAP_ONLY:
    return "Weapon only";
  case AT_RANDOM:
    return "Random";
  case NUM_ATTACK_TYPES:
    break;
  }
  ASSERT(false);
  return "";
}

// There is _flavour_base_desc function but it seems to be too verbose
static const char* _get_attack_flavour_short_description(attack_flavour flavour)
{
  // Note: Monster utility also prints damage for some flavours which could be useful for wiki as well
  switch (flavour)
  {
  case AF_PLAIN: return "Plain";
  case AF_ACID: return "Acid";
  case AF_BLINK: return "Blink";
  case AF_COLD: return "Cold";
  case AF_CONFUSE: return "Confuse";
#if TAG_MAJOR_VERSION == 34
  case AF_DISEASE: return "Disease";
  case AF_DRAIN_STR: return "Drain strength";
  case AF_DRAIN_INT: return "Drain intelligence";
  case AF_DRAIN_DEX: return "Drain dexterity";
  case AF_DRAIN_STAT: return "Drain stat";
#endif
  case AF_DRAIN: return "Drain experience";
  case AF_ELEC: return "Electricity";
  case AF_FIRE: return "Fire";
#if TAG_MAJOR_VERSION == 34
  case AF_HUNGER: return "Hunger";
  case AF_MUTATE: return "Mutate";
#endif
  case AF_POISON_PARALYSE: return "Paralyse";
  case AF_POISON: return "Poison";
#if TAG_MAJOR_VERSION == 34
  case AF_POISON_NASTY: return "Poison nasty";
  case AF_POISON_MEDIUM: return "Poison medium";
#endif
  case AF_POISON_STRONG: return "Strong poison";
#if TAG_MAJOR_VERSION == 34
  case AF_POISON_STR: return "Poison strength";
  case AF_POISON_INT: return "Poison intelligence";
  case AF_POISON_DEX: return "Poison dexterity";
  case AF_POISON_STAT: return "Poison stat";
  case AF_ROT: return "Rot";
#endif
  case AF_VAMPIRIC: return "Vampiric";
#if TAG_MAJOR_VERSION == 34
  case AF_KLOWN: return "Klown";
#endif
  case AF_DISTORT: return "Distort";
  case AF_RAGE: return "Rage";
#if TAG_MAJOR_VERSION == 34
  case AF_STICKY_FLAME: return "Sticky flame";
#endif
  case AF_CHAOTIC: return "Chaos";
  case AF_STEAL: return "Steal";
#if TAG_MAJOR_VERSION == 34
  case AF_STEAL_FOOD: return "Steal food";
#endif
  case AF_CRUSH: return "Crush";
  case AF_REACH: return "Reach";
  case AF_HOLY: return "Holy";
  case AF_ANTIMAGIC: return "Antimagic";
  case AF_PAIN: return "Pain";
  case AF_ENSNARE: return "Ensnare";
  case AF_FLOOD: return "Flood";
  case AF_PURE_FIRE: return "Pure fire";
  case AF_DRAIN_SPEED: return "Drain speed";
  case AF_VULN: return "Vuln";
#if TAG_MAJOR_VERSION == 34
  case AF_PLAGUE: return "Plague";
#endif
  case AF_REACH_STING: return "Reach sting";
  case AF_SHADOWSTAB: return "Shadow stab";
  case AF_DROWN: return "Drown";
#if TAG_MAJOR_VERSION == 34
  case AF_FIREBRAND: return "Firebrand";
#endif
  case AF_CORRODE: return "Corrode";
  case AF_SCARAB: return "Scarab";
#if TAG_MAJOR_VERSION == 34
  case AF_KITE: return "Kite";
#endif
  case AF_SWOOP: return "Swoop";
  case AF_TRAMPLE: return "Trample";
  case AF_WEAKNESS: return "Weakness";
#if TAG_MAJOR_VERSION == 34
  case AF_MIASMATA: return "Miasmata";
#endif
  case AF_REACH_TONGUE: return "Reach tongue";
  case AF_BLINK_WITH: return "Blink with";
  case AF_SEAR: return "Sear";
  case AF_BARBS: return "Barbs";
  case AF_SPIDER: return "Spider";
  case AF_RIFT: return "Rift";
  case AF_BLOODZERK: return "Bloodzerk";
  case AF_SLEEP: return "Sleep";
  case AF_MINIPARA: return "Minipara";
  case AF_FLANK: return "Flank";
  case AF_DRAG: return "Drag";
  case AF_FOUL_FLAME: return "Foul flame";
  case AF_HELL_HUNT: return "Hell hunt";
  case AF_SWARM: return "Swarm";
  case AF_ALEMBIC: return "Alembic";
  case AF_BOMBLET: return "Bomblet";
  case AF_AIRSTRIKE: return "Airstrike";
  case AF_TRICKSTER: return "Trickster";
  case AF_REACH_CLEAVE_UGLY: return "Reach cleave ugly";
  case AF_DOOM: return "Doom";
  case AF_SLIMIFY: return "Slimify";
  case AF_DIM: return "Dim";
  }
  return "";
}

static void _print_attack_info(monster& mon)
{
  mon.wield_melee_weapon();
  std::string monsterattacks;
  for (int x = 0; x < 4; x++)
  {
    int attack_num = x;
    if (mon.has_hydra_multi_attack())
      attack_num = x == 0 ? x : x + mon.number - 1;
    mon_attack_def attk = mons_attack_spec(mon, attack_num);
    if (!attk.type) {
      continue;
    }

    if (monsterattacks.empty())
    {
      monsterattacks = R"(  Attacks:
)";
    }

    short int dam = attk.damage;
    if (mon.berserk_or_frenzied() || mon.has_ench(ENCH_MIGHT))
      dam = dam * 3 / 2;

    if (mon.has_ench(ENCH_WEAK))
      dam = dam * 2 / 3;

    monsterattacks += make_stringf(R"(    -
      Damage: %d
      Type: "%s"
      Flavour: "%s"
)",
      dam,
      _get_mon_attack_type_description(attk.type),
      _get_attack_flavour_short_description(attk.flavour)); 

  }

  printf("%s", monsterattacks.c_str());
}

static void _print_monster_spell(monster& mp, spell_type spell, mon_spell_slot_flags flags, std::string override_damage = "", spell_type override_spell_type = SPELL_NO_SPELL)
{
  spell_type sp = override_spell_type != SPELL_NO_SPELL ? override_spell_type : spell;
  printf(R"(      -
        Spell: "%s"
)",
    spell_title(sp)
  );
  const auto dmg_str = !override_damage.empty() ? override_damage : mons_human_readable_spell_damage_string(&mp, spell);
  if (!dmg_str.empty()) {
      printf(R"(        Damage: "%s"
)", dmg_str.c_str());
  }
  printf(R"(        Flags: %s
)",
  _get_monster_spell_flags_description(flags).c_str()
);
}

static void _print_monster_spellsets(monster& mp, const std::set<std::vector<std::pair<spell_type, uint32_t>>>& spell_sets, const std::multimap<spell_type, std::string>& overriden_damages)
{
  if (spell_sets.empty()) {
    return;
  }
  // Spellsets always array of 1 currently:
  printf(R"(  Spellsets:
)");
  for (const auto& spell_set : spell_sets)
  {
    printf(R"(    -
)");
    for (const auto& p : spell_set)
    {
      const auto sp = p.first;
      const auto flags = mon_spell_slot_flags{ static_cast<mon_spell_slot_flag>(p.second) };
      if (spell_is_soh_breath(sp))
      {
        const vector<spell_type>* breaths = soh_breath_spells(sp);
        ASSERT(breaths);

        if (breaths)
        {
          for (auto breath : *breaths)
          {
            _print_monster_spell(mp, sp, flags, "", breath);
          }
        }
        continue;
      }
      std::string overriden_damage;
      auto its = overriden_damages.equal_range(sp);
      if (its.first != overriden_damages.end())
      {
        overriden_damage = "";
        for (auto it = its.first; it != its.second; ++it)
        {
          if (!overriden_damage.empty())
          {
            overriden_damage += " / ";
          }
          overriden_damage += it->second;
        }
      }
      _print_monster_spell(mp, sp, flags, overriden_damage);
    }
  }
}

static std::string _get_holiness_description (mon_holy_type holiness)
{
  std::string description;
  for (int i = MH_HOLY; i <= MH_LAST; i <<= 1) {
     auto flag = static_cast<mon_holy_type_flags>(i);
    if (holiness & flag) {
      if (!description.empty()) {
        description += " ";
      }
      description += single_holiness_description(flag);
    }
  }
  // weird quirk:
  if (description == "natural demonic")
  {
    return "Natural demon";
  }
  ASSERT(!description.empty());
  return uppercase_first(description);
}

static const char* _get_item_use_description(mon_itemuse_type itemuse)
{
  switch (itemuse)
  {
  case MONUSE_NOTHING:
    return R"(["Uses nothing"])";
  case MONUSE_OPEN_DOORS:
    return R"(["Open doors"])";
  case MONUSE_STARTING_EQUIPMENT:
    return R"(["Starting equipment", "Open doors"])";
  case MONUSE_WEAPONS_ARMOUR:
    return R"(["Weapons armour", "Starting equipment", "Open doors"])";
  case NUM_MONUSE:
    break;
  }
  return "";
}

static std::string _get_habitat_description(habitat_type habitat)
{
  switch (habitat)
  {
  case HT_LAND: return "Land";
  case HT_AMPHIBIOUS: return "Amphibious";
  case HT_WATER: return "Water";
  case HT_AMPHIBIOUS_LAVA: return "Amphibious lava";
  case HT_ELDRITCH_TENTACLE: return "Eldritch tentacle";
  case HT_FLYER: return "Flyer";
  case HT_LAVA: return "Lava";
  case HT_WALL: return "Wall";
  case HT_DEEP_WATER: return "Deep water";
  case HT_WALLS_ONLY: return "Walls only";
  default:
    break;
  }
  ASSERT(false);
  return "";
}

static const char* _get_monster_single_flag_description(monclass_flag_type flag)
{
  switch (flag) 
  {
  case M_NO_FLAGS:
    return "";
  case M_EAT_DOORS:
    return "Eats doors";
  case M_CRASH_DOORS:
    return "Crashes doors";
  case M_FLIES:
    return "Flying flag";
  case M_FIGHTER:
    return "Fighter flag";
  case M_NO_WAND:
    return "No wand flag";
  case M_NO_HT_WAND:
    return "No high tier wand flag";
  case M_INVIS:
    return "Invisible flag";
  case M_SEE_INVIS:
    return "See invisible flag";
  case M_UNBLINDABLE:
    return "Unblindable flag";
  case M_SPEAKS:
    return "Speaks flag";
  case M_CONFUSED:
    return "Confused flag";
  case M_BATTY:
    return "Batty flag";
  case M_SPLITS:
    return "Splits flag";
  case M_FRAGILE:
    return "Fragile flag";
  case M_STATIONARY:
    return "Stationary flag";
  case M_WEB_IMMUNE:
    return "Web immune flag";
  case M_COLD_BLOOD:
    return "Cold blood flag";
  case M_WARM_BLOOD:
    return "Warm blood flag";
  case M_GHOST_DEMON:
    return "Ghost demon flag";
  case M_BURROWS:
    return "Burrows flag";
  case M_HAS_AURA:
    return "Has aura flag";
  case M_UNIQUE:
    return "Unique flag";
  case M_ACID_SPLASH:
    return "Acid splash flag";
  case M_ARCHER:
    return "Archer flag";
  case M_INSUBSTANTIAL:
    return "Insubstantial flag";
  case M_TWO_WEAPONS:
    return "Two weapons flag";
  case M_FAST_REGEN:
    return "Regenerates flag";
  case M_NO_REGEN:
    return "No regenerate flag";
  case M_MALE:
    return "Male flag";
  case M_FEMALE:
    return "Female flag";
  case M_NO_SKELETON:
    return "No skeleton flag";
  case M_NO_EXP_GAIN:
    return "No exp gain flag";
  case M_SPINY:
    return "Spiny flag";
  case M_CAUTIOUS:
    return "Cautious flag";
  case M_NO_POLY_TO:
    return "No poly flag";
  case M_ANCESTOR:
    return "Ancestor flag";
  case M_PREFER_RANGED:
    return "Don't melee flag";
  case M_REMNANT:
    return "Remnant flag";
  case M_UNBREATHING:
    return "Unbreathing flag";
  case M_UNFINISHED:
    return "Unfinished flag";
  case M_HERD:
    return "Herd flag";
  case M_TALL_TILE:
    return "Tall tile flag";
  case M_UNSTABLE:
    return "Conjured flag"; // keep the old name for now
  case M_MAINTAIN_RANGE:
    return "Maintain range flag";
  case M_NO_ZOMBIE:
    return "No zombie flag";
  case M_CANT_SPAWN:
    return "Cant spawn flag";
  case M_NO_GEN_DERIVED:
    return "No gen derived flag";
  case M_PRIEST:
    return "Priest flag";
  case M_NAME_THE:
    return "Name the flag";
  case M_PROJECTILE:
    return "Projectile flag";
  case M_AVATAR:
    return "Avatar flag";
  case M_PERIPHERAL:
    return "Peripheral flag";
  case M_NO_THREAT:
    return "Harmless flag";
  case M_ALWAYS_WAND:
    return "Always wand flag";
  case M_GENDER_NEUTRAL:
    return "Gender neutral flag";
  case M_THUNDER_RING:
    return "Thunder ring flag";
  case M_FIRE_RING:
    return "Flame ring flag";
  case M_MIASMA_RING:
    return "Miasma ring flag";
  case M_AMORPHOUS:
    return "Amorphous flag";
  case M_WARDED:
    return "Warded flag";
  }
  return "";
}

static std::string _get_monster_flags_description(monclass_flags_t flags, monster& mon)
{
  std::string result;
  for (uint64_t i = 1; i <= std::numeric_limits<std::uint64_t>::max() / 2; i <<= 1) {
    const auto flag = static_cast<monclass_flag_type>(i);
    if (flags & flag) {
      _add_quoted_item(result, _get_monster_single_flag_description(flag));
    }
  }
  // Several derivative flags present in wiki
  if (mon.evil())
  {
    _add_quoted_item(result, "Evil flag");
  }
  if (mon.is_unbreathing())
  {
    _add_quoted_item(result, "Unbreathing flag");
  }
  return result;
}

static std::string _get_willpower_description(const monsterentry* me, const monsterentry *mbase, int hd)
{
  if (me->willpower == WILL_INVULN)
  {
    return "Immune";
  }
  if (me->willpower < 0)
  {
    // triggered only for pandemonium lord currently:
    return to_string(hd * (mbase ? mbase->willpower : me->willpower) * 4 / 3 * -1);
  }
  return  to_string(me->willpower);
}

static void _add_resist_vuln_line(int rval, const char *name, std::string &out_resists, std::string out_vulnerabilities)
{
  if (rval == 0)
  {
    return;
  }
  if (rval > 0)
  {
    if (rval == 1) {
      _add_quoted_item(out_resists, make_stringf("%s resistance", name));
    } else
    {
      _add_quoted_item(out_resists, make_stringf("%s resistance %d", name, rval));
    }
  }
  _add_quoted_item(out_vulnerabilities, make_stringf("%s vulnerability", name));
}

static void _print_resistances_and_vulnerabilities(resists_t res, monster& mon)
{
  std::string resists, vulnerabilities;
  static const std::pair<mon_resist_flags, const char*> flag_name_pairs[] = {
    {MR_RES_FIRE, "Fire"},
    {MR_RES_DAMNATION, "Damnation"},
    {MR_RES_COLD, "Cold"},
    {MR_RES_ELEC, "Electricity"},
    {MR_RES_POISON, "Poison"},
    {MR_RES_CORR, "Acid"},
    {MR_RES_STEAM, "Steam"}
  };
  for (auto p : flag_name_pairs)
  {
    _add_resist_vuln_line(get_resist(res, p.first), p.second, resists, vulnerabilities);
  }
  _add_resist_vuln_line(mon.res_water_drowning(), "Drown", resists, vulnerabilities);
  _add_resist_vuln_line(mon.res_miasma(), "Miasma", resists, vulnerabilities);
  _add_resist_vuln_line(mon.res_negative_energy(/*intrinsic_only*/true), "Negative energy", resists, vulnerabilities);
  _add_resist_vuln_line(mon.res_petrify(), "Petrify", resists, vulnerabilities);
  _add_resist_vuln_line(mon.res_holy_energy(), "Holy", resists, vulnerabilities);
  // currently missing in wiki:
  //_add_resist_vuln_line(mon.res_foul_flame(), "Foul flame", resists, vulnerabilities);
  _add_resist_vuln_line(mon.res_torment(), "Torment", resists, vulnerabilities);
  _add_resist_vuln_line(mon.res_polar_vortex(), "Vortex", resists, vulnerabilities);
  _add_resist_vuln_line(mon.res_sticky_flame(), "Sticky flame", resists, vulnerabilities);
  _add_resist_vuln_line(mon.how_chaotic() ? -1 : 0, "Silver", resists, vulnerabilities);

  if (!resists.empty())
  {
    printf("  Resistances: [%s]\n", resists.c_str());
  }
  if (!vulnerabilities.empty())
  {
    printf("  Vulnerabilities: [%s]\n", vulnerabilities.c_str());
  }
}

// roughly, parts from get_monster_db_desc
// draconian descriptions are not supported due to _describe_draconian being static
static void _get_monster_description_and_quote(const monster_info& mi, std::string &description, std::string &quote)
{
  string db_name;

  if (mi.props.exists(DBNAME_KEY))
    db_name = mi.props[DBNAME_KEY].get_string();
  else if (mi.mname.empty())
    db_name = mi.db_name();
  else
    db_name = mi.full_name(DESC_PLAIN);

  if (mons_species(mi.type) == MONS_SERPENT_OF_HELL)
    db_name += " " + serpent_of_hell_flavour(mi.type);
  if (mi.type == MONS_ORC_APOSTLE && mi.attitude == ATT_FRIENDLY)
    db_name = "orc apostle follower";

  description = getLongDescription(db_name);
  quote = getQuoteString(db_name);

  string symbol;
  symbol += get_monster_data(mi.type)->basechar;
  if (isaupper(symbol[0]))
    symbol = "cap-" + symbol;

  string quote2;
  if (!mons_is_unique(mi.type))
  {

    string symbol_suffix = "__" + symbol + "_suffix";
    quote2 = getQuoteString(symbol_suffix);
  }

  if (!quote.empty() && !quote2.empty())
    quote += "\n";
  quote += quote2;

  if (!mons_is_unique(mi.type))
  {
    string symbol_suffix = "__";
    symbol_suffix += symbol;
    symbol_suffix += "_suffix";

    string suffix = getLongDescription(symbol_suffix)
      + getLongDescription(symbol_suffix + "_examine");

    if (!suffix.empty())
      description += "\n" + suffix;
  }
}

static std::string _escape_characters(std::string str)
{
  str = replace_all(str, "\n", "\\n");
  str = replace_all(str, "\"", "\\\"");
  return str;
}

// postprocess string for descriptions and quotes
// trim whitespaces and escape characters
static std::string _postprocess_txt_str(std::string str)
{
  trim_string(str);
  return _escape_characters(str);
}

static void _print_mon_description_and_quote(const monster_info& mi)
{
  if (mi.type == MONS_PLAYER_ILLUSION || mi.type == MONS_PLAYER_GHOST)
  {
    return;
  }
  std::string description, quote;
  _get_monster_description_and_quote(mi, description, quote);
  if (!description.empty()) {
    _postprocess_txt_str(description);
    printf(R"(  Description: "%s"
)", description.c_str());
  }
  if (!quote.empty())
  {
    _postprocess_txt_str(quote);
    printf(R"(  Quote: "%s"
)", quote.c_str());
  }
}

static void _reset_monster(monster* mp)
{
  // If it was a unique or had unrands, let it/them generate in future
  // // iterations as well.
  for (int obj : mp->inv)
    if (obj != NON_ITEM) {
      set_unique_item_status(env.item[obj], UNIQ_NOT_EXISTS);
      env.item[obj].clear();
    }
  you.unique_creatures.set(mp->type, false);
  // Destroy the monster.
  mp->reset();
}

static std::string _convert_colour_str(const std::string& input)
{
  auto output = input;
  for (size_t i = 0; i < output.length(); ++i)
  {
    if (i == 0 || output[i - 1] == ' ')
      output[i] = toupper(output[i]);
  }
  output.erase(std::remove(output.begin(), output.end(), ' '), output.end());
  return output;
}

static bool _is_element_colour(int col)
{
  col = col & 0x007f;
  ASSERT(col < NUM_COLOURS);
  return col >= ETC_FIRE;
}

static std::string _specialize_name(std::string& name, monster_type spec_type)
{
  if (spec_type == MONS_BAI_SUZHEN_DRAGON) {
    return name + " (dragon)";
  }
  if (mons_species(spec_type) == MONS_SERPENT_OF_HELL) {
    // Remove "the" to not deal with renaming wiki pages for now:
    return name.substr(4) + make_stringf(" (%s)", branches[serpent_of_hell_branch(spec_type)].shortname);
  }
  return name;
}

static void _record_spell_damages(monster *mp, std::multimap<spell_type, std::string> &overriden_damages)
{
  for (int i = 0; i < 100; ++i)
  {
    for (const auto& slot : mp->spells)
    {
      auto dmg = mons_human_readable_spell_damage_string(mp, slot.spell);
      auto its = overriden_damages.equal_range(slot.spell);
      if (std::find_if(its.first, its.second, 
        [&dmg](const std::pair<const spell_type, std::string>& p) { return dmg == p.second; }) != its.second)
      {
        continue;
      }
      overriden_damages.insert(std::make_pair(slot.spell, dmg));
    }
  }
}

static std::vector<std::pair<spell_type, uint32_t>> _to_spell_set(const std::vector<mon_spell_slot> &slots)
{
  std::vector<std::pair<spell_type, uint32_t>> result;
  result.reserve(slots.size());
  for (const auto &slot : slots)
  {
    result.emplace_back(slot.spell, static_cast<uint32_t>(slot.flags.flags));
  }
  return result;
}

static void _print_data_for_monster(monster_type spec_type)
{
  const int ntrials = 100;

  long exp = 0L;
  int hp_min = 0;
  int hp_max = 0;
  int mac = 0;
  int mev = 0;
  int speed_min = 0, speed_max = 0;
  // Calculate averages.
  mons_spec spec{spec_type};
  int index = _mi_create_monster(spec);
  if (index == NON_MONSTER)
  {
    fprintf(stderr, R"(Unexpected failure generating monster for "%s"\n)", get_monster_data(spec_type)->name);
    exit(1);
  }

  std::multimap<spell_type, std::string> overriden_damages;
  std::set<std::vector<std::pair<spell_type, uint32_t>>> spell_sets;

  for (int i = 0; i < ntrials; ++i)
  {
    monster* mp = &env.mons[index];
    const string mname = mp->name(DESC_PLAIN, true);
    exp += exp_value(*mp);
    
    mac += mp->armour_class();
    mev += mp->evasion();
    set_min_max(mp->speed, speed_min, speed_max);
    set_min_max(mp->hit_points, hp_min, hp_max);
    // do generation similar to monster util for specific monsters to replicate current behaviour:
    if (spec_type == MONS_ASTERION || spec_type == MONS_CEREBOV || spec_type == MONS_DEMONSPAWN_BLOOD_SAINT)
    {
      _record_spell_damages(mp, overriden_damages);
    }
    // only tiamat still has different spell sets:
    if (spec_type == MONS_TIAMAT)
    {
      spell_sets.insert(_to_spell_set(mp->spells));
    }

    _reset_monster(mp);

    index = _mi_create_monster(spec);
    if (index == NON_MONSTER)
    {
      fprintf(stderr, "Unexpected failure generating monster for %s\n", spec.monname.c_str());
      exit(1);
    }
  }
  exp /= ntrials;
  mac /= ntrials;
  mev /= ntrials;

  monster& mon(env.mons[index]);
  if (!mon.spells.empty())
  {
    spell_sets.insert(_to_spell_set(mon.spells));
  }

  const bool shapeshifter = mon.is_shapeshifter()
    || spec_type == MONS_SHAPESHIFTER
    || spec_type == MONS_GLOWING_SHAPESHIFTER;

  const bool nonbase =
    mons_species(mon.type) == MONS_DRACONIAN && mon.type != MONS_DRACONIAN;

  const monsterentry* me =
    shapeshifter ? get_monster_data(spec_type) : mon.find_monsterentry();

  const monsterentry* mbase =
    nonbase ? get_monster_data(draconian_subspecies(mon))
    : (monsterentry*)0;

  if (!me) {
    _reset_monster(&mon);
    return;
  }

  string monsterresistances;
  string monstervulnerabilities;
  monster_info mi(&mon, MILEV_NAME);

  auto colour = mi.colour();
  if (_is_element_colour(colour))
    colour = element_colour(colour, coord_def(), true);

  const int hd = mon.get_experience_level();
  std::string name = mons_type_name(spec_type, DESC_PLAIN);
  name = _specialize_name(name, spec_type);
  printf(R"("%s":
  Name: "%s"
  Colour: "%s"
  Glyph: "%c"
  Speed: "%s"
  HD: %d
  "Average HP 10x": %d
  AC: %d
  EV: %d
)",
    name.c_str(),
    name.c_str(),
    _convert_colour_str(colour_to_str(colour, /*human readable*/true)).c_str(),
    me->basechar,
    monster_speed(mon, speed_min, speed_max).c_str(),
    hd,
    me->avg_hp_10x,
    mac,
    mev);

  _print_attack_info(mon);

  printf(R"(  Holiness: "%s"
  "Item Use": %s
  Habitat: "%s"
)", _get_holiness_description(me->holiness).c_str(),
  _get_item_use_description(me->gmon_use),
  _get_habitat_description(me->habitat).c_str()
  );

  _print_monster_spellsets(mon, spell_sets, overriden_damages);
  printf(R"(  Flags: [%s]
  Willpower: "%s"
)",
  _get_monster_flags_description(me->bitfields, mon).c_str(),
  _get_willpower_description(me, mbase, hd).c_str()
  );
  _print_resistances_and_vulnerabilities(shapeshifter ? me->resists :
    get_mons_resists(mon), mon);

  auto genus_mon = get_monster_data(me->genus);
  auto species_mon = get_monster_data(me->species);
  
  printf(R"(  XP: %ld
  Size: "%s"
  Intelligence: "%s"
  Genus: "%s"
  Species: "%s"
)",
    exp,
    uppercase_first(monster_size(mon)).c_str(),
    uppercase_first(monster_int(mon)).c_str(),
    genus_mon ? genus_mon->name : me->name,
    species_mon ? species_mon->name : me->name
  );
  _print_mon_description_and_quote(mi);

  _reset_monster(&mon);
}

static void _print_monsters()
{
  auto saved_generators = rng::generators_to_vector();

  for (int i = 0; i < NUM_MONSTERS; ++i)
  {
    rng::load_generators(saved_generators); // restore rng to have the same results as monster utility
    const auto spec_type = static_cast<monster_type>(i);
    auto entry = get_monster_data(spec_type);
    if (entry->bitfields & M_CANT_SPAWN) {
      continue;
    }
    _print_data_for_monster(spec_type);
  }
}

static void _print_description_and_quote(const std::string& db_name)
{
  auto description = getLongDescription(db_name);
  description = _postprocess_txt_str(description);
  if (!description.empty())
  {
    printf(R"(  description: "%s"
)", description.c_str());
  }

  auto quote = getQuoteString(db_name);
  quote = _postprocess_txt_str(quote);
  if (!quote.empty())
  {
    printf(R"(  quote: "%s"
)", quote.c_str());
  }
}

static void _print_spell_description_and_quote(const std::string& spell_name)
{
  _print_description_and_quote(spell_name + " spell");
}

static const char* _get_spell_flag_description(spflag flag)
{
  switch (flag)
  {
  case spflag::none:
    break;
  case spflag::dir_or_target:
    return "dir_or_target";
  case spflag::target:
    return "target";
  case spflag::prefer_farthest:
    return "prefer_farthest";
  case spflag::targeting_mask:
    return "targeting_mask";
  case spflag::obj:
    return "obj";
  case spflag::helpful:
    return "helpful";
  case spflag::aim_at_space:
    return "aim_at_space";
  case spflag::not_self:
    return "not_self";
  case spflag::unholy:
    return "unholy";
  case spflag::unclean:
    return "unclean";
  case spflag::chaotic:
    return "chaotic";
  case spflag::hasty:
    return "hasty";
  case spflag::silent:
    return "silent";
  case spflag::escape:
    return "escape";
  case spflag::recovery:
    return "recovery";
  case spflag::destructive:
    return "destructive";
  case spflag::selfench:
    return "selfench";
  case spflag::monster:
    return "monster";
  case spflag::needs_tracer:
    return "needs_tracer";
  case spflag::noisy:
    return "noisy";
  case spflag::testing:
    return "testing";
  case spflag::no_ghost:
    return "no_ghost";
  case spflag::cloud:
    return "cloud";
  case spflag::WL_check:
    return "WL_check";
  case spflag::mons_abjure:
    return "mons_abjure";
  case spflag::dummy:
    return "dummy";
  case spflag::holy:
    return "holy";
  }
  return "";
}

static void _print_spell_flags(spell_type spell)
{
  const spell_flags flags = get_spell_flags(spell);
  using underlying_type = std::underlying_type<spflag>::type;
  printf("  flags:\n");
  for (underlying_type i = 1; i <= std::numeric_limits<underlying_type>::max() / 2; i <<= 1)
  {
    const auto flag = static_cast<spflag>(i);
    if (flags & flag)
    {
      printf("    %s: true\n", _get_spell_flag_description(flag));
    }
  }
}

static void _print_spell_schools(spell_type spell)
{
  printf("  schools:\n");
  for (const auto school : spschools_type::range())
  {
    if (spell_typematch(spell, school))
    {
      printf(R"(    "%s": true
)", spelltype_long_name(school));
    }
  }
}

static void _print_spell_range(spell_type spell)
{
  const auto min_range = spell_range(spell, &you, 0);
  const auto cap = spell_power_cap(spell);
  const auto max_range = spell_range(spell, &you, cap);
  if (min_range == -1 || max_range == -1)
  {
    return;
  }
  printf(R"(  range:
    min: %d
    max: %d
)", min_range, max_range);
}

static void _print_spell_noise(spell_type spell)
{
  // from spell_noise_string in spl-cast.cc
  int effect_noise = spell_effect_noise(spell);
  if (spell == SPELL_POLAR_VORTEX)
    effect_noise = 15;

  printf(R"(  noise:
    casting: %d
    effect: %d
)", spell_noise(spell), effect_noise);
}

static string _get_book_name(book_type book)
{
  item_def item;
  item.base_type = OBJ_BOOKS;
  item.sub_type = book;
  return item.name(DESC_PLAIN, false, true);
}

static void _print_spell_books(spell_type spell)
{
  bool first = true;
  for (int i = 0; i < NUM_BOOKS; ++i)
  {
    auto book = static_cast<book_type>(i);
    if (!book_exists(book))
      continue;
    for (spell_type book_spell : spellbook_template(book))
    {
      if (spell == book_spell)
      {
        if (first)
        {
          printf("  books:\n");
          first = false;
        }
        printf(R"(    "%s": true
)", _get_book_name(book).c_str());
      }
    }
  }
}

static void _print_spell(spell_type spell)
{
  const std::string name = spell_title(spell);
  printf(R"("%s":
  name: "%s"
  level: %d
  "power cap": %d
)", name.c_str(),
  name.c_str(),
  spell_difficulty(spell),
  spell_power_cap(spell));
  _print_spell_range(spell);
  _print_spell_noise(spell);
  _print_spell_schools(spell);
  _print_spell_flags(spell);
  _print_spell_description_and_quote(name);
  _print_spell_books(spell);
}

static void _print_spells()
{
  _print_spell(SPELL_LEHUDIBS_CRYSTAL_SPEAR);
  for (int i = SPELL_NO_SPELL + 1; i < NUM_SPELLS; ++i)
  {
    const spell_type spell = static_cast<spell_type>(i);
    if (!is_valid_spell(spell) || !is_player_book_spell(spell))
      continue;

    _print_spell(spell);
  }
}

static void _print_book_spells(book_type book)
{
  printf("  spells:\n");
  for (const spell_type spell : spellbook_template(book))
  {
    printf(R"(    - "%s"
)", spell_title(spell));
  }
}

static void _print_book(book_type book)
{
  item_def item;
  item.base_type = OBJ_BOOKS;
  item.sub_type = book;
  item.quantity = 1;
  const auto name = _get_book_name(book);
  printf(R"("%s":
  name: "%s"
  value: %u
)",
    name.c_str(), name.c_str(), item_value(item, true));
  _print_book_spells(book);
  _print_description_and_quote(name);
}

static void _print_spellbooks()
{
  for (int i = 0; i < NUM_BOOKS; ++i)
  {
    auto book = static_cast<book_type>(i);
    if (!book_exists(book))
      continue;
    _print_book(book);
  }
}

int main(int argc, char* argv[])
{
    crawl_state.test = true;
    if (argc < 2 || argc > 3)
    {
        fprintf(stderr, "Usage: wiki <info type> <optional: path to crawl dir>\n");
        return 1;
    }

    if (argc >= 3)
    {
      SysEnv.crawl_base = argv[2];
    } else
    {
      SysEnv.crawl_base = ".";
    }
    initialize_crawl();

    string action = argv[1];
    if (action == "monsters")
    {
      _print_monsters();
    }
    else if (action == "spells")
    {
      _print_spells();
    }
    else if (action == "spellbooks")
    {
      _print_spellbooks();
    }
    else
    {
      fprintf(stderr, "Unsupported info type, currently supported: monsters");
      return 1;
    }
    return 0;
}
